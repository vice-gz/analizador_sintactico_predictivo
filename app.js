/* ==========================================================================
   VISUALIZADOR DE ANALIZADOR SINTÁCTICO PREDICTIVO LL(1)
   JavaScript Vanilla (ES6+) — Sin dependencias externas
   ========================================================================== */

(() => {
  'use strict';

  /* ------------------------------------------------------------------------
     1. CONSTANTES Y EJEMPLOS PRECARGADOS
     ------------------------------------------------------------------------ */
  const EPSILON = 'ε';
  const EOF = '$';
  const MAX_SIM_STEPS = 500;

  const PRESETS = {
    expressions: {
      name: 'Ejemplo 1: Expresiones',
      grammar: [
        "E -> T E'",
        "E' -> + T E' | ε",
        "T -> F T'",
        "T' -> * F T' | ε",
        'F -> ( E ) | id'
      ].join('\n'),
      samples: ['id+id', 'id*id', 'id+id*id', '(id+id)*id', 'id+*id']
    },
    ab: {
      name: 'Ejemplo 2: Cadenas a y b',
      grammar: 'S -> a S b | ε',
      samples: ['ab', 'aabb', 'aaabbb', 'aab', 'abb']
    }
  };

  /* ------------------------------------------------------------------------
     2. ESTADO GLOBAL DE LA APLICACIÓN
     ------------------------------------------------------------------------ */
  let activePresetKey = 'expressions';
  let currentGrammar = null;
  let currentFirst = null;
  let currentFollow = null;
  let currentMatrixData = null;

  let simState = {
    tokens: [],
    ptr: 0,
    stack: [],
    stepCount: 0,
    trace: [],
    status: 'idle', // 'idle' | 'running' | 'accepted' | 'rejected'
    verdictReason: '',
    activeCell: null, // { nt, col, isError } | null
    lastStackDiff: { popped: null, pushedCount: 0 }
  };

  /* ------------------------------------------------------------------------
     3. REFERENCIAS AL DOM
     ------------------------------------------------------------------------ */
  const dom = {
    presetButtons: document.querySelectorAll('.btn-preset'),
    grammarInput: document.getElementById('grammar-input'),
    grammarError: document.getElementById('grammar-error'),
    btnBuildGrammar: document.getElementById('btn-build-grammar'),
    ll1StatusPill: document.getElementById('ll1-status-pill'),
    ntCount: document.getElementById('nt-count'),
    tCount: document.getElementById('t-count'),
    nonTerminalsList: document.getElementById('non-terminals-list'),
    terminalsList: document.getElementById('terminals-list'),
    firstTableBody: document.getElementById('first-table-body'),
    followTableBody: document.getElementById('follow-table-body'),
    conflictBanner: document.getElementById('conflict-banner'),
    conflictList: document.getElementById('conflict-list'),
    matrixActiveIndicator: document.getElementById('matrix-active-indicator'),
    matrixHead: document.getElementById('matrix-head'),
    matrixBody: document.getElementById('matrix-body'),
    testStringInput: document.getElementById('test-string-input'),
    suggestedStringsWrap: document.getElementById('suggested-strings-wrap'),
    suggestedStringsList: document.getElementById('suggested-strings-list'),
    btnAnalyzeAll: document.getElementById('btn-analyze-all'),
    btnNextStep: document.getElementById('btn-next-step'),
    btnResetSim: document.getElementById('btn-reset-sim'),
    simStepCounter: document.getElementById('sim-step-counter'),
    tokenTape: document.getElementById('token-tape'),
    verdictBanner: document.getElementById('verdict-banner'),
    verdictIcon: document.getElementById('verdict-icon'),
    verdictTitle: document.getElementById('verdict-title'),
    verdictDetail: document.getElementById('verdict-detail'),
    stackVisual: document.getElementById('stack-visual'),
    traceTableBody: document.getElementById('trace-table-body'),
    traceScrollContainer: document.getElementById('trace-scroll-container')
  };

  /* ------------------------------------------------------------------------
     4. MÓDULO DE ANÁLISIS DE GRAMÁTICA (PARSEO Y EXTRACCIÓN LÉXICA)
     ------------------------------------------------------------------------ */

  /**
   * Normaliza variantes textuales de epsilon a 'ε'.
   * @param {string} token
   * @returns {string}
   */
  function normalizeSymbol(token) {
    if (/^(ε|ϵ|epsilon)$/i.test(token)) {
      return EPSILON;
    }
    return token;
  }

  /**
   * Parsea el texto de producciones ingresado por el usuario.
   * Soporta '->', '→', '|', 'ε' y 'epsilon', así como símbolos compuestos (id, E', T').
   * @param {string} rawText
   * @returns {object} Estructura de gramática analizada
   */
  function parseGrammar(rawText) {
    const lines = rawText
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter((line) => line.length > 0);

    if (lines.length === 0) {
      throw new Error('Ingresa al menos una producción para construir el analizador.');
    }

    const parsedLines = [];
    const nonTerminals = [];
    const ntSet = new Set();

    // Primera pasada: validar sintaxis de líneas y recolectar todos los No Terminales
    lines.forEach((line, idx) => {
      const match = line.match(/^(.*?)(?:->|→)(.*)$/);
      if (!match) {
        throw new Error(`Línea ${idx + 1}: falta el operador de producción ("->" o "→").`);
      }

      const lhs = match[1].trim();
      const rhsRaw = match[2].trim();

      if (!lhs) {
        throw new Error(`Línea ${idx + 1}: falta el símbolo No Terminal a la izquierda de la flecha.`);
      }
      if (/\s/.test(lhs)) {
        throw new Error(`Línea ${idx + 1}: el lado izquierdo "${lhs}" debe ser un único símbolo No Terminal sin espacios.`);
      }
      if (lhs === EPSILON || /^epsilon$/i.test(lhs) || lhs === EOF || lhs === '|') {
        throw new Error(`Línea ${idx + 1}: "${lhs}" no es un nombre válido para un No Terminal.`);
      }
      if (!rhsRaw) {
        throw new Error(`Línea ${idx + 1}: falta el lado derecho de la producción para "${lhs}".`);
      }

      if (!ntSet.has(lhs)) {
        ntSet.add(lhs);
        nonTerminals.push(lhs);
      }

      parsedLines.push({ lineNum: idx + 1, lhs, rhsRaw });
    });

    // Segunda pasada: separar alternativas por '|' y extraer tokens preservando símbolos compuestos
    const productions = [];
    const productionsByLhs = new Map();
    nonTerminals.forEach((nt) => productionsByLhs.set(nt, []));

    let prodId = 0;

    parsedLines.forEach(({ lineNum, lhs, rhsRaw }) => {
      const alternatives = rhsRaw.split('|');

      alternatives.forEach((alt) => {
        const trimmedAlt = alt.trim();
        if (!trimmedAlt) {
          throw new Error(`Línea ${lineNum}: existe una alternativa vacía alrededor de "|" en "${lhs}".`);
        }

        const rawTokens = trimmedAlt.split(/\s+/).map(normalizeSymbol);
        // Si ε aparece mezclado con otros símbolos, lo limpiamos; si es solo ε, lo conservamos
        const nonEpsTokens = rawTokens.filter((tok) => tok !== EPSILON);
        const rhs = nonEpsTokens.length === 0 ? [EPSILON] : nonEpsTokens;

        if (rhs.includes(EOF)) {
          throw new Error(`Línea ${lineNum}: el símbolo reservado "${EOF}" no debe escribirse manualmente en las producciones.`);
        }

        const production = {
          id: prodId++,
          lhs,
          rhs,
          text: `${lhs} -> ${rhs.join(' ')}`
        };

        productions.push(production);
        productionsByLhs.get(lhs).push(production);
      });
    });

    // Extraer Terminales automáticamente en orden de aparición
    const terminals = [];
    const tSet = new Set();

    productions.forEach((prod) => {
      prod.rhs.forEach((sym) => {
        if (sym !== EPSILON && !ntSet.has(sym) && !tSet.has(sym)) {
          tSet.add(sym);
          terminals.push(sym);
        }
      });
    });

    return {
      startSymbol: nonTerminals[0],
      nonTerminals,
      ntSet,
      terminals,
      tSet,
      productions,
      productionsByLhs
    };
  }

  /* ------------------------------------------------------------------------
     5. CÁLCULO DE CONJUNTOS FIRST
     ------------------------------------------------------------------------ */

  /**
   * Calcula FIRST(α) para una secuencia de símbolos α = X1 X2 ... Xk.
   * @param {string[]} sequence
   * @param {Map<string, Set<string>>} firstSets
   * @param {Set<string>} ntSet
   * @returns {Set<string>}
   */
  function computeFirstOfSequence(sequence, firstSets, ntSet) {
    const result = new Set();

    if (!sequence || sequence.length === 0 || (sequence.length === 1 && sequence[0] === EPSILON)) {
      result.add(EPSILON);
      return result;
    }

    let allNullable = true;

    for (const sym of sequence) {
      if (sym === EPSILON) {
        continue;
      }

      if (!ntSet.has(sym)) {
        // Símbolo terminal
        result.add(sym);
        allNullable = false;
        break;
      }

      const symFirst = firstSets.get(sym);
      if (symFirst) {
        symFirst.forEach((s) => {
          if (s !== EPSILON) result.add(s);
        });
      }

      if (!symFirst || !symFirst.has(EPSILON)) {
        allNullable = false;
        break;
      }
    }

    if (allNullable) {
      result.add(EPSILON);
    }

    return result;
  }

  /**
   * Calcula el conjunto FIRST para cada No Terminal mediante algoritmo de punto fijo.
   * @param {object} grammar
   * @returns {Map<string, Set<string>>}
   */
  function computeFirstSets(grammar) {
    const firstSets = new Map();
    grammar.nonTerminals.forEach((nt) => firstSets.set(nt, new Set()));

    let changed = true;
    while (changed) {
      changed = false;

      for (const prod of grammar.productions) {
        const targetSet = firstSets.get(prod.lhs);
        const seqFirst = computeFirstOfSequence(prod.rhs, firstSets, grammar.ntSet);

        seqFirst.forEach((sym) => {
          if (!targetSet.has(sym)) {
            targetSet.add(sym);
            changed = true;
          }
        });
      }
    }

    return firstSets;
  }

  /* ------------------------------------------------------------------------
     6. CÁLCULO DE CONJUNTOS FOLLOW
     ------------------------------------------------------------------------ */

  /**
   * Calcula el conjunto FOLLOW para cada No Terminal (incluyendo '$').
   * @param {object} grammar
   * @param {Map<string, Set<string>>} firstSets
   * @returns {Map<string, Set<string>>}
   */
  function computeFollowSets(grammar, firstSets) {
    const followSets = new Map();
    grammar.nonTerminals.forEach((nt) => followSets.set(nt, new Set()));

    // Regla 1: colocar '$' en FOLLOW del símbolo inicial
    followSets.get(grammar.startSymbol).add(EOF);

    let changed = true;
    while (changed) {
      changed = false;

      for (const prod of grammar.productions) {
        if (prod.rhs.length === 1 && prod.rhs[0] === EPSILON) {
          continue;
        }

        const lhsFollow = followSets.get(prod.lhs);

        for (let i = 0; i < prod.rhs.length; i++) {
          const sym = prod.rhs[i];
          if (!grammar.ntSet.has(sym)) {
            continue;
          }

          const symFollow = followSets.get(sym);
          const beta = prod.rhs.slice(i + 1);

          if (beta.length > 0) {
            const firstBeta = computeFirstOfSequence(beta, firstSets, grammar.ntSet);

            // Regla 2: todo lo de FIRST(β) excepto ε pasa a FOLLOW(B)
            firstBeta.forEach((s) => {
              if (s !== EPSILON && !symFollow.has(s)) {
                symFollow.add(s);
                changed = true;
              }
            });

            // Regla 3: si β =>* ε, entonces FOLLOW(A) pasa a FOLLOW(B)
            if (firstBeta.has(EPSILON)) {
              lhsFollow.forEach((s) => {
                if (!symFollow.has(s)) {
                  symFollow.add(s);
                  changed = true;
                }
              });
            }
          } else {
            // Regla 3: B está al final de A -> α B
            lhsFollow.forEach((s) => {
              if (!symFollow.has(s)) {
                symFollow.add(s);
                changed = true;
              }
            });
          }
        }
      }
    }

    return followSets;
  }

  /* ------------------------------------------------------------------------
     7. CONSTRUCCIÓN DE MATRIZ PREDICTIVA LL(1) Y DETECCIÓN DE CONFLICTOS
     ------------------------------------------------------------------------ */

  /**
   * Detecta recursividad por la izquierda directa e indirecta.
   * Construye el grafo de derivación más a la izquierda (considerando prefijos anulables).
   * @param {object} grammar
   * @param {Map<string, Set<string>>} firstSets
   * @returns {Array<{ type: string, nt: string, cycle: string[] }>}
   */
  function detectLeftRecursion(grammar, firstSets) {
    const graph = new Map();
    grammar.nonTerminals.forEach((nt) => graph.set(nt, new Set()));

    for (const prod of grammar.productions) {
      if (prod.rhs[0] === EPSILON) continue;

      for (const sym of prod.rhs) {
        if (grammar.ntSet.has(sym)) {
          graph.get(prod.lhs).add(sym);
          if (!firstSets.get(sym).has(EPSILON)) {
            break;
          }
        } else {
          break;
        }
      }
    }

    const recursions = [];
    const seenCycles = new Set();

    for (const startNt of grammar.nonTerminals) {
      // Recursividad directa: A ->* A α en 1 paso
      if (graph.get(startNt).has(startNt)) {
        const key = `direct:${startNt}`;
        if (!seenCycles.has(key)) {
          seenCycles.add(key);
          recursions.push({
            type: 'directa',
            nt: startNt,
            cycle: [startNt, startNt]
          });
        }
        continue;
      }

      // Recursividad indirecta mediante BFS buscando el ciclo más corto de regreso a startNt
      const queue = [];
      const visited = new Set();

      graph.get(startNt).forEach((neighbor) => {
        queue.push([startNt, neighbor]);
        visited.add(neighbor);
      });

      while (queue.length > 0) {
        const path = queue.shift();
        const current = path[path.length - 1];

        for (const next of graph.get(current)) {
          if (next === startNt) {
            const fullCycle = [...path, startNt];
            const canonical = [...new Set(path)].sort().join('|');
            const key = `indirect:${canonical}`;
            if (!seenCycles.has(key)) {
              seenCycles.add(key);
              recursions.push({
                type: 'indirecta',
                nt: startNt,
                cycle: fullCycle
              });
            }
            queue.length = 0;
            break;
          }
          if (!visited.has(next)) {
            visited.add(next);
            queue.push([...path, next]);
          }
        }
      }
    }

    return recursions;
  }

  /**
   * Construye la matriz predictiva LL(1) y recopila todos los conflictos detectados.
   * @param {object} grammar
   * @param {Map<string, Set<string>>} firstSets
   * @param {Map<string, Set<string>>} followSets
   * @returns {object}
   */
  function buildParsingTable(grammar, firstSets, followSets) {
    const columns = [...grammar.terminals, EOF];
    const table = {};

    grammar.nonTerminals.forEach((nt) => {
      table[nt] = {};
      columns.forEach((col) => {
        table[nt][col] = [];
      });
    });

    const insertEntry = (nt, col, prod, source) => {
      const cell = table[nt][col];
      if (!cell) return;
      // Evita duplicar la misma producción exacta en la misma celda
      const existing = cell.find((item) => item.prod.id === prod.id);
      if (!existing) {
        cell.push({ prod, source });
      }
    };

    for (const prod of grammar.productions) {
      const firstAlpha = computeFirstOfSequence(prod.rhs, firstSets, grammar.ntSet);

      // Para cada terminal a en FIRST(α), añadir A -> α en M[A, a]
      firstAlpha.forEach((sym) => {
        if (sym !== EPSILON) {
          insertEntry(prod.lhs, sym, prod, 'FIRST');
        }
      });

      // Si ε ∈ FIRST(α), para cada b en FOLLOW(A), añadir A -> α en M[A, b]
      if (firstAlpha.has(EPSILON)) {
        const followA = followSets.get(prod.lhs);
        followA.forEach((sym) => {
          insertEntry(prod.lhs, sym, prod, 'FOLLOW');
        });
      }
    }

    // Recolectar conflictos en celdas
    const cellConflicts = [];
    for (const nt of grammar.nonTerminals) {
      for (const col of columns) {
        const entries = table[nt][col];
        if (entries.length > 1) {
          const hasFirst = entries.some((e) => e.source === 'FIRST');
          const hasFollow = entries.some((e) => e.source === 'FOLLOW');
          let kind = 'FIRST/FIRST (prefijo común o ambigüedad)';
          if (hasFirst && hasFollow) {
            kind = 'FIRST/FOLLOW (conflicto entre derivar y anular con ε)';
          } else if (!hasFirst && hasFollow) {
            kind = 'FOLLOW/FOLLOW (múltiples derivaciones anulables)';
          }

          cellConflicts.push({
            nt,
            col,
            kind,
            productions: entries.map((e) => e.prod.text)
          });
        }
      }
    }

    const leftRecursions = detectLeftRecursion(grammar, firstSets);
    const isLL1 = cellConflicts.length === 0 && leftRecursions.length === 0;

    return {
      columns,
      table,
      cellConflicts,
      leftRecursions,
      isLL1
    };
  }

  /* ------------------------------------------------------------------------
     8. TOKENIZADOR DE CADENAS DE ENTRADA (LONGEST-MATCH)
     ------------------------------------------------------------------------ */

  /**
   * Tokeniza la cadena de entrada usando los terminales de la gramática ordenados
   * de mayor a menor longitud, evitando separar tokens compuestos como 'id'.
   * @param {string} rawInput
   * @param {string[]} terminals
   * @returns {Array<{ value: string, isUnknown: boolean }>}
   */
  function tokenizeInput(rawInput, terminals) {
    const sortedTerminals = [...terminals].sort((a, b) => b.length - a.length);
    const tokens = [];
    let pos = 0;

    while (pos < rawInput.length) {
      // Omitir espacios en blanco
      if (/\s/.test(rawInput[pos])) {
        pos++;
        continue;
      }

      // Si el usuario escribió '$' explícitamente al final, no lo duplicamos
      if (rawInput.slice(pos).trim() === EOF) {
        break;
      }

      let matched = null;
      for (const term of sortedTerminals) {
        if (rawInput.startsWith(term, pos)) {
          matched = term;
          break;
        }
      }

      if (matched !== null) {
        tokens.push({ value: matched, isUnknown: false });
        pos += matched.length;
      } else {
        // Capturar secuencia contigua no reconocida hasta un espacio o terminal válido
        let end = pos + 1;
        while (end < rawInput.length && !/\s/.test(rawInput[end])) {
          const startsKnown = sortedTerminals.some((term) => rawInput.startsWith(term, end));
          if (startsKnown) break;
          end++;
        }
        tokens.push({ value: rawInput.slice(pos, end), isUnknown: true });
        pos = end;
      }
    }

    tokens.push({ value: EOF, isUnknown: false });
    return tokens;
  }

  /* ------------------------------------------------------------------------
     9. MOTOR DE SIMULACIÓN DEL ANALIZADOR PREDICTIVO LL(1)
     ------------------------------------------------------------------------ */

  /**
   * Reinicia la simulación con la cadena actual en el campo de texto.
   */
  function resetSimulation() {
    if (!currentGrammar) return;

    const rawInput = dom.testStringInput.value;
    const tokens = tokenizeInput(rawInput, currentGrammar.terminals);

    simState = {
      tokens,
      ptr: 0,
      stack: [EOF, currentGrammar.startSymbol],
      stepCount: 0,
      trace: [],
      status: 'idle',
      verdictReason: '',
      activeCell: null,
      lastStackDiff: { popped: null, pushedCount: 0 }
    };

    highlightSampleButton(rawInput);
    renderSimulationView({ animateStack: false, animateLatestRow: false });
  }

  /**
   * Ejecuta exactamente un paso del analizador sintáctico predictivo con pila.
   * @returns {boolean} true si se ejecutó un paso, false si la simulación ya terminó.
   */
  function executeOneStep() {
    if (!currentGrammar || !currentMatrixData) return false;
    if (simState.status === 'accepted' || simState.status === 'rejected') return false;

    simState.status = 'running';
    simState.stepCount += 1;

    const stackSnapshot = simState.stack.join(' ');
    const inputSnapshot = simState.tokens
      .slice(simState.ptr)
      .map((t) => t.value)
      .join(' ');

    // Protección ante posibles bucles infinitos en gramáticas no LL(1)
    if (simState.stepCount > MAX_SIM_STEPS) {
      simState.status = 'rejected';
      simState.verdictReason = `Se superó el límite de ${MAX_SIM_STEPS} pasos (posible derivación infinita en la gramática).`;
      simState.activeCell = null;
      simState.lastStackDiff = { popped: null, pushedCount: 0 };
      simState.trace.push({
        stackText: stackSnapshot,
        inputText: inputSnapshot,
        actionText: 'Error: límite de pasos excedido',
        actionType: 'error'
      });
      return true;
    }

    const top = simState.stack[simState.stack.length - 1];
    const currentTok = simState.tokens[simState.ptr];
    const lookahead = currentTok ? currentTok.value : EOF;

    // 1. Verificar símbolo desconocido en el token actual
    if (currentTok && currentTok.isUnknown) {
      simState.status = 'rejected';
      simState.verdictReason = `Error léxico: el símbolo "${lookahead}" no pertenece al conjunto de terminales de la gramática.`;
      simState.activeCell = null;
      simState.lastStackDiff = { popped: null, pushedCount: 0 };
      simState.trace.push({
        stackText: stackSnapshot,
        inputText: inputSnapshot,
        actionText: `Error: símbolo '${lookahead}' no reconocido`,
        actionType: 'error'
      });
      return true;
    }

    // 2. Caso de aceptación: tope es '$' y entrada actual es '$'
    if (top === EOF && lookahead === EOF) {
      simState.status = 'accepted';
      simState.verdictReason = 'La cadena pertenece al lenguaje generado por la gramática. La pila y la entrada llegaron simultáneamente a "$".';
      simState.activeCell = null;
      simState.lastStackDiff = { popped: null, pushedCount: 0 };
      simState.trace.push({
        stackText: stackSnapshot,
        inputText: inputSnapshot,
        actionText: 'ACEPTADA',
        actionType: 'accept'
      });
      return true;
    }

    // 3. Caso terminal o '$' en el tope de la pila
    if (!currentGrammar.ntSet.has(top)) {
      simState.activeCell = null;

      if (top === lookahead) {
        simState.stack.pop();
        simState.ptr += 1;
        simState.lastStackDiff = { popped: top, pushedCount: 0 };
        simState.trace.push({
          stackText: stackSnapshot,
          inputText: inputSnapshot,
          actionText: `Emparejar '${top}'`,
          actionType: 'match'
        });
      } else {
        simState.status = 'rejected';
        if (top === EOF) {
          simState.verdictReason = `Error de coincidencia: la pila llegó al fondo "${EOF}", pero aún quedan símbolos sin consumir en la entrada (se encontró "${lookahead}").`;
        } else if (lookahead === EOF) {
          simState.verdictReason = `Error de coincidencia: la cadena terminó inesperadamente ("${EOF}"), pero en el tope de la pila se esperaba "${top}".`;
        } else {
          simState.verdictReason = `Error de coincidencia: en el tope de la pila se esperaba "${top}", pero el símbolo actual de entrada es "${lookahead}".`;
        }
        simState.lastStackDiff = { popped: null, pushedCount: 0 };
        simState.trace.push({
          stackText: stackSnapshot,
          inputText: inputSnapshot,
          actionText: `Error: esperaba '${top}', encontró '${lookahead}'`,
          actionType: 'error'
        });
      }
      return true;
    }

    // 4. Caso No Terminal en el tope de la pila: consultar M[top, lookahead]
    const cellEntries = currentMatrixData.table[top]
      ? currentMatrixData.table[top][lookahead]
      : null;

    if (!cellEntries || cellEntries.length === 0) {
      simState.status = 'rejected';
      simState.activeCell = { nt: top, col: lookahead, isError: true };
      simState.verdictReason = `Error sintáctico: la celda M[${top}, ${lookahead}] en la matriz predictiva está vacía (no existe producción para "${top}" con el símbolo actual "${lookahead}").`;
      simState.lastStackDiff = { popped: null, pushedCount: 0 };
      simState.trace.push({
        stackText: stackSnapshot,
        inputText: inputSnapshot,
        actionText: `Error: celda M[${top}, ${lookahead}] vacía`,
        actionType: 'error'
      });
      return true;
    }

    if (cellEntries.length > 1) {
      const competing = cellEntries.map((e) => e.prod.text).join(' ; ');
      simState.status = 'rejected';
      simState.activeCell = { nt: top, col: lookahead, isError: true };
      simState.verdictReason = `Conflicto LL(1) en M[${top}, ${lookahead}]: existen ${cellEntries.length} producciones posibles (${competing}). El analizador predictivo requiere una gramática determinista.`;
      simState.lastStackDiff = { popped: null, pushedCount: 0 };
      simState.trace.push({
        stackText: stackSnapshot,
        inputText: inputSnapshot,
        actionText: `Error: conflicto LL(1) en M[${top}, ${lookahead}]`,
        actionType: 'error'
      });
      return true;
    }

    // Producción única válida: desapilar No Terminal y apilar RHS en orden inverso
    const prod = cellEntries[0].prod;
    simState.activeCell = { nt: top, col: lookahead, isError: false };
    simState.stack.pop();

    let pushedCount = 0;
    if (!(prod.rhs.length === 1 && prod.rhs[0] === EPSILON)) {
      for (let i = prod.rhs.length - 1; i >= 0; i--) {
        simState.stack.push(prod.rhs[i]);
        pushedCount++;
      }
    }

    simState.lastStackDiff = { popped: top, pushedCount };
    simState.trace.push({
      stackText: stackSnapshot,
      inputText: inputSnapshot,
      actionText: `Aplicar ${prod.text}`,
      actionType: 'rule'
    });

    return true;
  }

  /**
   * Ejecuta la simulación completa hasta llegar a ACEPTADA o RECHAZADA.
   */
  function analyzeComplete() {
    if (!currentGrammar) return;

    // Si ya había finalizado una corrida anterior, reinicia antes de analizar completo
    if (simState.status === 'accepted' || simState.status === 'rejected') {
      resetSimulation();
    }

    while (simState.status !== 'accepted' && simState.status !== 'rejected') {
      const progressed = executeOneStep();
      if (!progressed) break;
    }

    renderSimulationView({ animateStack: true, animateLatestRow: true });
  }

  /* ------------------------------------------------------------------------
     10. MÓDULO DE ACTUALIZACIÓN DEL DOM
     ------------------------------------------------------------------------ */

  /**
   * Crea un elemento DOM de forma segura.
   */
  function createEl(tag, className, textContent) {
    const el = document.createElement(tag);
    if (className) el.className = className;
    if (textContent !== undefined) el.textContent = textContent;
    return el;
  }

  /**
   * Muestra u oculta el mensaje de error de sintaxis de la gramática.
   */
  function setGrammarError(message) {
    if (!message) {
      dom.grammarError.classList.add('hidden');
      dom.grammarError.textContent = '';
    } else {
      dom.grammarError.textContent = message;
      dom.grammarError.classList.remove('hidden');
    }
  }

  /**
   * Renderiza los badges de No Terminales y Terminales + estado LL(1).
   */
  function renderLexicalBadges(grammar, matrixData) {
    dom.ntCount.textContent = String(grammar.nonTerminals.length);
    dom.tCount.textContent = String(grammar.terminals.length);

    dom.nonTerminalsList.innerHTML = '';
    grammar.nonTerminals.forEach((nt, index) => {
      const badge = createEl('span', 'symbol-badge symbol-badge--nt');
      badge.appendChild(document.createTextNode(nt));
      if (index === 0) {
        badge.appendChild(createEl('span', 'symbol-badge--start-tag', 'Inicial'));
      }
      dom.nonTerminalsList.appendChild(badge);
    });

    dom.terminalsList.innerHTML = '';
    if (grammar.terminals.length === 0) {
      dom.terminalsList.appendChild(createEl('span', 'hint-inline', 'Sin terminales explícitos (solo ε)'));
    } else {
      grammar.terminals.forEach((t) => {
        dom.terminalsList.appendChild(createEl('span', 'symbol-badge symbol-badge--t', t));
      });
    }

    if (matrixData.isLL1) {
      dom.ll1StatusPill.textContent = 'LL(1) Válida';
      dom.ll1StatusPill.className = 'status-pill status-pill--valid';
    } else {
      dom.ll1StatusPill.textContent = 'No es LL(1) · Conflictos';
      dom.ll1StatusPill.className = 'status-pill status-pill--conflict';
    }
  }

  /**
   * Renderiza las tablas de conjuntos FIRST y FOLLOW.
   */
  function renderFirstFollowTables(grammar, firstSets, followSets) {
    const renderSetTable = (tbody, setsMap) => {
      tbody.innerHTML = '';
      grammar.nonTerminals.forEach((nt) => {
        const tr = document.createElement('tr');
        const tdNt = createEl('td', 'nt-cell-label', nt);
        const tdSet = document.createElement('td');
        const chipsWrap = createEl('div', 'set-chips');

        const values = Array.from(setsMap.get(nt) || []);
        if (values.length === 0) {
          chipsWrap.appendChild(createEl('span', 'hint-inline', '∅'));
        } else {
          values.forEach((sym) => {
            let chipClass = 'set-chip';
            if (sym === EPSILON) chipClass += ' set-chip--eps';
            else if (sym === EOF) chipClass += ' set-chip--eof';
            chipsWrap.appendChild(createEl('span', chipClass, sym));
          });
        }

        tdSet.appendChild(chipsWrap);
        tr.append(tdNt, tdSet);
        tbody.appendChild(tr);
      });
    };

    renderSetTable(dom.firstTableBody, firstSets);
    renderSetTable(dom.followTableBody, followSets);
  }

  /**
   * Muestra el banner de alerta cuando la gramática presenta conflictos LL(1)
   * o recursividad por la izquierda.
   */
  function renderConflictBanner(matrixData) {
    dom.conflictList.innerHTML = '';

    if (matrixData.isLL1) {
      dom.conflictBanner.classList.add('hidden');
      return;
    }

    matrixData.leftRecursions.forEach((rec) => {
      const li = document.createElement('li');
      const strong = createEl('strong', null, `Recursividad por la izquierda ${rec.type}: `);
      const code = createEl('code', null, rec.cycle.join(' → '));
      li.append(strong, code, document.createTextNode(' (una gramática recursiva por la izquierda no puede analizarse con LL(1)).'));
      dom.conflictList.appendChild(li);
    });

    matrixData.cellConflicts.forEach((conf) => {
      const li = document.createElement('li');
      const cellCode = createEl('code', null, `M[${conf.nt}, ${conf.col}]`);
      const prodsCode = createEl('code', null, conf.productions.join('  |  '));
      li.append(
        document.createTextNode('Conflicto '),
        createEl('strong', null, conf.kind),
        document.createTextNode(' en '),
        cellCode,
        document.createTextNode(': '),
        prodsCode
      );
      dom.conflictList.appendChild(li);
    });

    dom.conflictBanner.classList.remove('hidden');
  }

  /**
   * Construye la tabla HTML de la Matriz Predictiva LL(1).
   */
  function renderParsingMatrix(grammar, matrixData) {
    dom.matrixHead.innerHTML = '';
    dom.matrixBody.innerHTML = '';

    // Cabecera de columnas: Terminales + '$'
    const headRow = document.createElement('tr');
    headRow.appendChild(createEl('th', null, 'NT \\ T'));

    matrixData.columns.forEach((col) => {
      const th = createEl('th', null, col);
      th.dataset.colHeader = col;
      headRow.appendChild(th);
    });
    dom.matrixHead.appendChild(headRow);

    // Filas: No Terminales
    grammar.nonTerminals.forEach((nt) => {
      const tr = document.createElement('tr');
      const thRow = createEl('th', null, nt);
      thRow.dataset.rowHeader = nt;
      tr.appendChild(thRow);

      matrixData.columns.forEach((col) => {
        const entries = matrixData.table[nt][col];
        const td = createEl('td', 'matrix-cell');
        td.dataset.nt = nt;
        td.dataset.col = col;

        if (!entries || entries.length === 0) {
          td.classList.add('matrix-cell--empty');
          td.textContent = '—';
        } else {
          if (entries.length > 1) {
            td.classList.add('matrix-cell--conflict');
          }
          entries.forEach((entry) => {
            td.appendChild(createEl('span', 'matrix-prod', entry.prod.text));
          });
        }

        tr.appendChild(td);
      });

      dom.matrixBody.appendChild(tr);
    });
  }

  /**
   * Sincroniza y resalta la celda [No Terminal, Terminal Actual] en la matriz predictiva.
   */
  function highlightActiveMatrixCell(activeCell) {
    // Limpiar resaltados previos
    dom.matrixHead.querySelectorAll('.matrix-header--active').forEach((el) => {
      el.classList.remove('matrix-header--active');
    });
    dom.matrixBody.querySelectorAll('.matrix-row-header--active').forEach((el) => {
      el.classList.remove('matrix-row-header--active');
    });
    dom.matrixBody.querySelectorAll('.matrix-cell--active, .matrix-cell--active-error').forEach((el) => {
      el.classList.remove('matrix-cell--active', 'matrix-cell--active-error');
    });

    if (!activeCell) {
      dom.matrixActiveIndicator.classList.add('hidden');
      dom.matrixActiveIndicator.textContent = '';
      return;
    }

    dom.matrixActiveIndicator.textContent = `Consultando M[${activeCell.nt}, ${activeCell.col}]`;
    dom.matrixActiveIndicator.classList.remove('hidden');

    // Resaltar cabecera de columna
    dom.matrixHead.querySelectorAll('[data-col-header]').forEach((th) => {
      if (th.dataset.colHeader === activeCell.col) {
        th.classList.add('matrix-header--active');
      }
    });

    // Resaltar cabecera de fila
    dom.matrixBody.querySelectorAll('[data-row-header]').forEach((th) => {
      if (th.dataset.rowHeader === activeCell.nt) {
        th.classList.add('matrix-row-header--active');
      }
    });

    // Resaltar celda exacta (forzando reinicio de animación para pulsos consecutivos)
    const cells = dom.matrixBody.querySelectorAll('td[data-nt]');
    for (const td of cells) {
      if (td.dataset.nt === activeCell.nt && td.dataset.col === activeCell.col) {
        void td.offsetWidth;
        td.classList.add(activeCell.isError ? 'matrix-cell--active-error' : 'matrix-cell--active');
        break;
      }
    }
  }

  /**
   * Renderiza los botones rápidos de cadenas de prueba del ejemplo activo.
   */
  function renderSuggestedStrings(presetKey) {
    dom.suggestedStringsList.innerHTML = '';

    if (!presetKey || !PRESETS[presetKey]) {
      dom.suggestedStringsWrap.classList.add('hidden');
      return;
    }

    dom.suggestedStringsWrap.classList.remove('hidden');
    PRESETS[presetKey].samples.forEach((sample) => {
      const btn = createEl('button', 'btn-sample', sample);
      btn.type = 'button';
      btn.dataset.sample = sample;
      btn.addEventListener('click', () => {
        dom.testStringInput.value = sample;
        resetSimulation();
      });
      dom.suggestedStringsList.appendChild(btn);
    });
  }

  /**
   * Marca visualmente qué cadena sugerida coincide con el input actual.
   */
  function highlightSampleButton(currentValue) {
    const trimmed = currentValue.trim();
    dom.suggestedStringsList.querySelectorAll('.btn-sample').forEach((btn) => {
      btn.classList.toggle('is-selected', btn.dataset.sample === trimmed);
    });
  }

  /**
   * Renderiza la cinta de tokens indicando los ya consumidos y el símbolo actual.
   */
  function renderTokenTape(tokens, ptr, status) {
    dom.tokenTape.innerHTML = '';

    tokens.forEach((tok, idx) => {
      const span = createEl('span', 'tape-token', tok.value);
      if (tok.isUnknown) {
        span.classList.add('tape-token--unknown');
      }
      if (idx < ptr || (status === 'accepted' && idx <= ptr)) {
        span.classList.add('tape-token--consumed');
      } else if (idx === ptr && status !== 'accepted') {
        span.classList.add('tape-token--current');
      }
      dom.tokenTape.appendChild(span);
    });
  }

  /**
   * Clasifica el estilo visual de un símbolo dentro de la pila.
   */
  function getStackItemClass(sym, grammar) {
    if (sym === EOF) return 'stack-item--eof';
    if (grammar && grammar.ntSet.has(sym)) return 'stack-item--nt';
    return 'stack-item--t';
  }

  /**
   * Renderiza la pila sintáctica con animaciones fluidas de push y pop (transform + opacity).
   */
  function renderVisualStack(stack, grammar, diff, animate) {
    dom.stackVisual.innerHTML = '';

    const pushStartIndex = animate && diff.pushedCount > 0
      ? Math.max(0, stack.length - diff.pushedCount)
      : stack.length;

    stack.forEach((sym, idx) => {
      const isTop = idx === stack.length - 1;
      const item = createEl('div', `stack-item ${getStackItemClass(sym, grammar)}`);
      if (isTop) item.classList.add('stack-item--top');

      if (animate && idx >= pushStartIndex) {
        item.classList.add('stack-item--push');
        item.style.animationDelay = `${(idx - pushStartIndex) * 45}ms`;
      }

      const label = createEl('span', null, sym);
      let roleText = 'T';
      if (sym === EOF) roleText = 'EOF';
      else if (grammar && grammar.ntSet.has(sym)) roleText = 'NT';
      if (isTop) roleText = 'TOPE';

      const badge = createEl('span', 'stack-item__badge', roleText);
      item.append(label, badge);
      dom.stackVisual.appendChild(item);
    });

    // Efecto visual no bloqueante del elemento recién desapilado (pop)
    if (animate && diff.popped) {
      const ghost = createEl(
        'div',
        `stack-item ${getStackItemClass(diff.popped, grammar)} stack-item--popping`
      );
      ghost.append(
        createEl('span', null, diff.popped),
        createEl('span', 'stack-item__badge', 'POP')
      );
      dom.stackVisual.appendChild(ghost);

      const cleanup = () => {
        if (ghost.parentNode) ghost.parentNode.removeChild(ghost);
      };
      ghost.addEventListener('animationend', cleanup, { once: true });
      setTimeout(cleanup, 340);
    }
  }

  /**
   * Renderiza la tabla de traza con las 3 columnas exactas:
   * Pila | Entrada Pendiente | Acción / Regla Aplicada
   */
  function renderTraceTable(trace, animateLatest) {
    dom.traceTableBody.innerHTML = '';

    if (trace.length === 0) {
      const tr = createEl('tr', 'trace-empty-row');
      const td = createEl(
        'td',
        null,
        'Presiona "Siguiente Paso" o "Analizar Completo" para iniciar la simulación.'
      );
      td.colSpan = 3;
      tr.appendChild(td);
      dom.traceTableBody.appendChild(tr);
      return;
    }

    trace.forEach((row, idx) => {
      const isLatest = idx === trace.length - 1;
      const tr = document.createElement('tr');
      if (isLatest) {
        tr.classList.add('trace-row--latest');
        if (animateLatest) tr.classList.add('trace-row--new');
      }

      const tdStack = createEl('td', null, row.stackText);
      const tdInput = createEl('td', null, row.inputText);
      const tdAction = document.createElement('td');
      tdAction.appendChild(createEl('span', `action-tag action-tag--${row.actionType}`, row.actionText));

      tr.append(tdStack, tdInput, tdAction);
      dom.traceTableBody.appendChild(tr);
    });

    dom.traceScrollContainer.scrollTop = dom.traceScrollContainer.scrollHeight;
  }

  /**
   * Renderiza el banner de veredicto final (ACEPTADA / RECHAZADA).
   */
  function renderVerdictBanner(status, reason) {
    if (status !== 'accepted' && status !== 'rejected') {
      dom.verdictBanner.classList.add('hidden');
      dom.verdictBanner.classList.remove('verdict-banner--accepted', 'verdict-banner--rejected');
      return;
    }

    const isAccepted = status === 'accepted';
    dom.verdictBanner.classList.remove('hidden', 'verdict-banner--accepted', 'verdict-banner--rejected');
    void dom.verdictBanner.offsetWidth; // reinicia animación CSS
    dom.verdictBanner.classList.add(isAccepted ? 'verdict-banner--accepted' : 'verdict-banner--rejected');

    dom.verdictIcon.textContent = isAccepted ? '✓' : '✕';
    dom.verdictTitle.textContent = isAccepted ? 'CADENA ACEPTADA' : 'CADENA RECHAZADA';
    dom.verdictDetail.textContent = reason;
  }

  /**
   * Sincroniza todos los elementos visuales de la sección de simulación y la matriz.
   */
  function renderSimulationView({ animateStack, animateLatestRow }) {
    dom.simStepCounter.textContent = `Paso ${simState.stepCount}`;

    const isFinished = simState.status === 'accepted' || simState.status === 'rejected';
    dom.btnNextStep.disabled = !currentGrammar || isFinished;
    dom.btnAnalyzeAll.disabled = !currentGrammar;
    dom.btnResetSim.disabled = !currentGrammar;

    renderTokenTape(simState.tokens, simState.ptr, simState.status);
    renderVisualStack(simState.stack, currentGrammar, simState.lastStackDiff, animateStack);
    renderTraceTable(simState.trace, animateLatestRow);
    renderVerdictBanner(simState.status, simState.verdictReason);
    highlightActiveMatrixCell(simState.activeCell);
  }

  /* ------------------------------------------------------------------------
     11. FLUJO PRINCIPAL DE CONSTRUCCIÓN Y EVENTOS
     ------------------------------------------------------------------------ */

  /**
   * Procesa la gramática actual: parsea, calcula FIRST/FOLLOW, arma matriz y reinicia simulador.
   */
  function buildAnalyzerFromInput() {
    setGrammarError('');

    try {
      const grammar = parseGrammar(dom.grammarInput.value);
      const firstSets = computeFirstSets(grammar);
      const followSets = computeFollowSets(grammar, firstSets);
      const matrixData = buildParsingTable(grammar, firstSets, followSets);

      currentGrammar = grammar;
      currentFirst = firstSets;
      currentFollow = followSets;
      currentMatrixData = matrixData;

      renderLexicalBadges(grammar, matrixData);
      renderFirstFollowTables(grammar, firstSets, followSets);
      renderConflictBanner(matrixData);
      renderParsingMatrix(grammar, matrixData);
      resetSimulation();
    } catch (err) {
      setGrammarError(err.message);
    }
  }

  /**
   * Carga uno de los ejemplos precargados junto con sus cadenas sugeridas.
   */
  function loadPreset(presetKey) {
    const preset = PRESETS[presetKey];
    if (!preset) return;

    activePresetKey = presetKey;
    dom.presetButtons.forEach((btn) => {
      btn.classList.toggle('is-active', btn.dataset.preset === presetKey);
    });

    dom.grammarInput.value = preset.grammar;
    dom.testStringInput.value = preset.samples[0];
    renderSuggestedStrings(presetKey);
    buildAnalyzerFromInput();
  }

  /**
   * Registra los escuchadores de eventos de la interfaz.
   */
  function bindEvents() {
    dom.presetButtons.forEach((btn) => {
      btn.addEventListener('click', () => loadPreset(btn.dataset.preset));
    });

    // Si el usuario edita manualmente la gramática, desmarcar botón de preset activo
    dom.grammarInput.addEventListener('input', () => {
      const currentText = dom.grammarInput.value.trim();
      let matchedPreset = null;

      Object.keys(PRESETS).forEach((key) => {
        if (PRESETS[key].grammar.trim() === currentText) {
          matchedPreset = key;
        }
      });

      activePresetKey = matchedPreset;
      dom.presetButtons.forEach((btn) => {
        btn.classList.toggle('is-active', btn.dataset.preset === matchedPreset);
      });
      renderSuggestedStrings(matchedPreset);
    });

    dom.btnBuildGrammar.addEventListener('click', buildAnalyzerFromInput);

    dom.testStringInput.addEventListener('input', () => {
      resetSimulation();
    });

    dom.testStringInput.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') {
        e.preventDefault();
        analyzeComplete();
      }
    });

    dom.btnNextStep.addEventListener('click', () => {
      if (executeOneStep()) {
        renderSimulationView({ animateStack: true, animateLatestRow: true });
      }
    });

    dom.btnAnalyzeAll.addEventListener('click', analyzeComplete);
    dom.btnResetSim.addEventListener('click', resetSimulation);
  }

  // Inicialización al cargar la página
  bindEvents();
  loadPreset('expressions');
})();

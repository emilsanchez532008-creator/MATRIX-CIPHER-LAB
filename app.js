"use strict";

window.MathJax = {
    tex: { inlineMath: [['\\(', '\\)']], displayMath: [['\\[', '\\]']] },
    startup: { typeset: false }
};

const ALPHABET = "ABCDEFGHIJKLMNÑOPQRSTUVWXYZ";
const CHAR_TO_NUM = Object.fromEntries(Array.from(ALPHABET, (char, index) => [char, index + 1]));
const NUM_TO_CHAR = Object.fromEntries(Array.from(ALPHABET, (char, index) => [index + 1, char]));
const MAX_DIMENSION = 6;
const LAST_KEY_STORAGE = "matrixCipherLab.lastKey.v1";
const SCRAMBLE_CHARACTERS = "ABCDEFGHIJKLMNÑOPQRSTUVWXYZ#%*0123456789";
let uploadedCipher = null;
let lastDecryptedText = "";
let downloadUrl = null;
let lastEncryptionKey = null;
let copyResetTimer = null;
let counterPulseTimer = null;
let previousCharacterCount = 0;
let encodingRun = 0;
const rippleTimers = new WeakMap();
const buttonAnimationTimers = new WeakMap();

function byId(id) {
    return document.getElementById(id);
}

function showScreen(screen) {
    const names = ["landing", "encrypt-screen", "decrypt-screen", "guide-screen"];
    const selected = screen === "encrypt" ? "encrypt-screen"
        : screen === "decrypt" ? "decrypt-screen"
        : screen === "guide" ? "guide-screen" : "landing";
    const updateView = () => {
        names.forEach((name) => { byId(name).hidden = name !== selected; });
        byId("switch-button").hidden = screen !== "encrypt" && screen !== "decrypt";
        byId("switch-button").textContent = screen === "encrypt" ? "↔ Descifrar" : "↔ Encriptar";
    };
    const scrollToTop = () => window.scrollTo({ top: 0, behavior: "smooth" });
    if (document.startViewTransition && !window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
        document.startViewTransition(updateView).finished.then(scrollToTop);
    } else {
        updateView();
        const activeScreen = byId(selected);
        activeScreen.classList.remove("screen-enter");
        void activeScreen.offsetWidth;
        activeScreen.classList.add("screen-enter");
        activeScreen.addEventListener("animationend", () => activeScreen.classList.remove("screen-enter"), { once: true });
        scrollToTop();
    }
}

function getDimension(prefix) {
    return Number(byId(`${prefix}-dim`).value);
}

function setDimension(prefix, dimension) {
    byId(`${prefix}-dim`).value = String(dimension);
    buildMatrixEditor(prefix);
}

function animateCells(container, confirm = false, pop = false) {
    Array.from(container.querySelectorAll(".matrix-input, .cipher-input")).forEach((input, index) => {
        input.classList.remove("matrix-cell-enter", "matrix-cell-pop", "key-cell-pulse");
        input.style.setProperty("--stagger-delay", `${Math.min(index * 24, 600)}ms`);
        void input.offsetWidth;
        input.classList.add(pop ? "matrix-cell-pop" : "matrix-cell-enter");
        if (confirm) input.classList.add("key-cell-pulse");
    });
}

function animateButton(button, className, duration) {
    const timer = buttonAnimationTimers.get(button);
    if (timer) clearTimeout(timer);
    button.classList.remove(className);
    void button.offsetWidth;
    button.classList.add(className);
    buttonAnimationTimers.set(button, setTimeout(() => button.classList.remove(className), duration));
}

function sweepMathView(element) {
    element.classList.remove("scan-sweep");
    void element.offsetWidth;
    element.classList.add("scan-sweep");
}

function fillMatrixEditor(prefix, matrix, confirm = false, pop = false) {
    matrix.forEach((row, rowIndex) => {
        row.forEach((value, colIndex) => {
            byId(`${prefix}-mat-${rowIndex}-${colIndex}`).value = String(value);
        });
    });
    validateKeyMatrix(prefix);
    animateCells(byId(`${prefix}-matrix-editor`), confirm, pop);
}

function buildMatrixEditor(prefix) {
    const dimension = getDimension(prefix);
    const editor = byId(`${prefix}-matrix-editor`);
    editor.replaceChildren();
    editor.style.gridTemplateColumns = `repeat(${dimension}, minmax(0, 1fr))`;
    for (let row = 0; row < dimension; row += 1) {
        for (let col = 0; col < dimension; col += 1) {
            const input = document.createElement("input");
            input.type = "number";
            input.step = "1";
            input.inputMode = "numeric";
            input.id = `${prefix}-mat-${row}-${col}`;
            input.className = "matrix-input";
            input.setAttribute("aria-label", `A fila ${row + 1}, columna ${col + 1}`);
            input.value = row === col ? "1" : "0";
            input.addEventListener("input", () => validateKeyMatrix(prefix));
            editor.appendChild(input);
        }
    }
    validateKeyMatrix(prefix);
    animateCells(editor);
    if (prefix === "enc") updateMessageLimit();
    if (prefix === "dec") buildCipherEditor();
}

function readMatrix(prefix) {
    const dimension = getDimension(prefix);
    const values = [];
    for (let row = 0; row < dimension; row += 1) {
        const matrixRow = [];
        for (let col = 0; col < dimension; col += 1) {
            const raw = byId(`${prefix}-mat-${row}-${col}`).value.trim();
            if (raw === "") return { valid: false, error: "Completa todas las celdas con números enteros." };
            const value = Number(raw);
            if (!Number.isSafeInteger(value)) return { valid: false, error: "La matriz debe contener solo enteros válidos." };
            matrixRow.push(value);
        }
        values.push(matrixRow);
    }
    return { valid: true, matrix: values };
}

// Bareiss mantiene el determinante exacto para matrices de enteros.
function determinantInteger(matrix) {
    const size = matrix.length;
    if (size === 0 || matrix.some((row) => row.length !== size)) throw new Error("La matriz clave debe ser cuadrada.");
    const work = matrix.map((row) => row.map((value) => BigInt(value)));
    let sign = 1n;
    let previousPivot = 1n;
    for (let pivotIndex = 0; pivotIndex < size - 1; pivotIndex += 1) {
        let pivotRow = pivotIndex;
        while (pivotRow < size && work[pivotRow][pivotIndex] === 0n) pivotRow += 1;
        if (pivotRow === size) return 0n;
        if (pivotRow !== pivotIndex) {
            [work[pivotIndex], work[pivotRow]] = [work[pivotRow], work[pivotIndex]];
            sign = -sign;
        }
        const pivot = work[pivotIndex][pivotIndex];
        for (let row = pivotIndex + 1; row < size; row += 1) {
            for (let col = pivotIndex + 1; col < size; col += 1) {
                const numerator = work[row][col] * pivot - work[row][pivotIndex] * work[pivotIndex][col];
                work[row][col] = numerator / previousPivot;
            }
            work[row][pivotIndex] = 0n;
        }
        previousPivot = pivot;
    }
    return sign * work[size - 1][size - 1];
}

function inverseMatrix(matrix) {
    const size = matrix.length;
    const work = matrix.map((row, index) => [
        ...row.map(Number),
        ...Array.from({ length: size }, (_, col) => index === col ? 1 : 0)
    ]);
    for (let col = 0; col < size; col += 1) {
        let pivotRow = col;
        for (let row = col + 1; row < size; row += 1) {
            if (Math.abs(work[row][col]) > Math.abs(work[pivotRow][col])) pivotRow = row;
        }
        if (work[pivotRow][col] === 0) throw new Error("No se pudo calcular la inversa de esta matriz.");
        [work[col], work[pivotRow]] = [work[pivotRow], work[col]];
        const pivot = work[col][col];
        for (let index = 0; index < size * 2; index += 1) work[col][index] /= pivot;
        for (let row = 0; row < size; row += 1) {
            if (row === col) continue;
            const factor = work[row][col];
            for (let index = 0; index < size * 2; index += 1) {
                work[row][index] -= factor * work[col][index];
            }
        }
    }
    return work.map((row) => row.slice(size));
}

function validateKeyMatrix(prefix) {
    const editor = byId(`${prefix}-matrix-editor`);
    const status = byId(`${prefix}-matrix-status`);
    const result = readMatrix(prefix);
    if (!result.valid) {
        editor.classList.remove("valid");
        editor.classList.add("invalid");
        status.className = "matrix-status invalid";
        status.textContent = `✕ ${result.error}`;
        return null;
    }
    const determinant = determinantInteger(result.matrix);
    if (determinant === 0n) {
        editor.classList.remove("valid");
        editor.classList.add("invalid");
        status.className = "matrix-status invalid";
        status.textContent = "✕ det(A) = 0: la matriz no tiene inversa.";
        return null;
    }
    editor.classList.remove("invalid");
    editor.classList.add("valid");
    status.className = "matrix-status valid";
    status.textContent = `✓ Matriz invertible · det(A) = ${determinant.toString()}`;
    return { matrix: result.matrix, determinant };
}

function randomInvertibleMatrix(prefix) {
    animateButton(byId("enc-random"), "rolling", 760);
    const dimension = getDimension(prefix);
    const matrix = Array.from({ length: dimension }, (_, row) =>
        Array.from({ length: dimension }, (_, col) => row === col ? 1 : 0));
    for (let operation = 0; operation < dimension * 3; operation += 1) {
        let target = Math.floor(Math.random() * dimension);
        let source = Math.floor(Math.random() * dimension);
        while (source === target) source = Math.floor(Math.random() * dimension);
        const factor = Math.floor(Math.random() * 5) - 2 || 1;
        for (let col = 0; col < dimension; col += 1) {
            matrix[target][col] += factor * matrix[source][col];
        }
    }
    fillMatrixEditor(prefix, matrix, false, true);
}

function buildCipherEditor(values = null) {
    const dimension = getDimension("dec");
    const editor = byId("dec-cipher-editor");
    editor.replaceChildren();
    editor.style.gridTemplateColumns = `repeat(${dimension}, minmax(0, 1fr))`;
    for (let row = 0; row < dimension; row += 1) {
        for (let col = 0; col < dimension; col += 1) {
            const input = document.createElement("input");
            input.type = "number";
            input.step = "1";
            input.inputMode = "numeric";
            input.id = `dec-b-${row}-${col}`;
            input.className = "cipher-input";
            input.setAttribute("aria-label", `B fila ${row + 1}, columna ${col + 1}`);
            input.placeholder = "0";
            if (values) input.value = String(values[row][col]);
            input.addEventListener("input", () => {
                if (uploadedCipher) {
                    uploadedCipher = null;
                    setFileStatus("Se editaron los valores: se usará la matriz B manual.", true);
                }
            });
            editor.appendChild(input);
        }
    }
    animateCells(editor);
}

function readCipherMatrix() {
    const dimension = getDimension("dec");
    const matrix = [];
    for (let row = 0; row < dimension; row += 1) {
        const matrixRow = [];
        for (let col = 0; col < dimension; col += 1) {
            const raw = byId(`dec-b-${row}-${col}`).value.trim();
            if (raw === "") return { valid: false, error: "Completa todas las celdas de la matriz B con enteros." };
            const value = Number(raw);
            if (!Number.isSafeInteger(value)) {
                return { valid: false, error: "La matriz B debe contener solo enteros válidos." };
            }
            matrixRow.push(value);
        }
        matrix.push(matrixRow);
    }
    return { valid: true, matrix };
}

function multiplyMatrices(left, right) {
    const rows = left.length;
    const inner = right.length;
    const cols = right[0].length;
    if (left.some((row) => row.length !== inner)) throw new Error("Las dimensiones no permiten multiplicar estas matrices.");
    const integerInputs = left.flat().every(Number.isSafeInteger) && right.flat().every(Number.isSafeInteger);
    return Array.from({ length: rows }, (_, row) =>
        Array.from({ length: cols }, (_, col) => {
            let sum = 0;
            for (let index = 0; index < inner; index += 1) {
                const product = left[row][index] * right[index][col];
                if (integerInputs && (!Number.isSafeInteger(product) || !Number.isSafeInteger(sum + product))) {
                    throw new Error("El resultado excede la precisión segura. Usa valores de clave más pequeños.");
                }
                sum += product;
            }
            return sum;
        }));
}

function formatDotProduct(left, right) {
    return left.map((value, index) => `(${value}) × (${right[index]})`).join(" + ");
}

function matrixLatex(matrix, decimals = false) {
    const rows = matrix.map((row) => row.map((value) => {
        if (!decimals || Number.isInteger(value)) return String(value);
        return Number(value.toFixed(5)).toString();
    }).join(" & "));
    return `\\begin{bmatrix}${rows.join(" \\\\ ")}\\end{bmatrix}`;
}

async function renderMath(element, latex) {
    element.innerHTML = `\\[${latex}\\]`;
    if (window.MathJax && window.MathJax.typesetPromise) {
        await window.MathJax.typesetPromise([element]);
    }
}

function normalizedCharacter(character) {
    if (character === " " || character === "Ñ" || character === "ñ") return character;
    const decomposed = character.normalize("NFD");
    const base = decomposed[0];
    const marks = decomposed.slice(1);
    if (base.toUpperCase() === "N" && marks.includes("\u0303")) return base === "n" ? "ñ" : "Ñ";
    const normalized = decomposed.replace(/[\u0300-\u036f]/g, "");
    if (/^[A-Za-z]$/.test(normalized)) return normalized;
    return null;
}

function sanitizeMessage(raw) {
    let value = "";
    let rejected = false;
    for (const character of raw.normalize("NFC")) {
        const normalized = normalizedCharacter(character);
        if (normalized === null) rejected = true;
        else value += normalized;
    }
    return { value, rejected };
}

function updateMessageLimit() {
    const limit = getDimension("enc") ** 2;
    const textarea = byId("enc-text");
    textarea.maxLength = limit;
    if (textarea.value.length > limit) textarea.value = textarea.value.slice(0, limit);
    byId("enc-limit-label").textContent = `máximo ${limit} caracteres`;
    updateMessageCounter(false);
}

function updateMessageCounter(rejected) {
    const limit = getDimension("enc") ** 2;
    const current = byId("enc-text").value.length;
    const counter = byId("enc-counter");
    const progress = byId("enc-character-progress");
    const fill = byId("enc-character-progress-fill");
    const ratio = limit ? current / limit : 0;
    counter.textContent = `${current} / ${limit} caracteres`;
    counter.parentElement.classList.toggle("warning", rejected);
    counter.parentElement.classList.toggle("near-limit", ratio >= 0.8 && current < limit);
    counter.parentElement.classList.toggle("at-limit", current === limit);
    progress.setAttribute("aria-valuemax", String(limit));
    progress.setAttribute("aria-valuenow", String(current));
    fill.style.width = `${ratio * 100}%`;
    if (current > previousCharacterCount && ratio >= 0.8) {
        counter.parentElement.classList.remove("capacity-pulse");
        void counter.parentElement.offsetWidth;
        counter.parentElement.classList.add("capacity-pulse");
        clearTimeout(counterPulseTimer);
        counterPulseTimer = setTimeout(() => counter.parentElement.classList.remove("capacity-pulse"), 420);
    }
    previousCharacterCount = current;
    byId("enc-input-warning").textContent = rejected ? "Se quitaron caracteres no admitidos." : "";
}

// X se llena por filas; el JSON conserva longitud y mayúsculas para restaurar espacios finales.
function makeMessageMatrix(text, dimension) {
    const values = Array.from(text, (character) => character === " " ? 0 : CHAR_TO_NUM[character.toUpperCase()]);
    const padded = [...values, ...Array(dimension * dimension - values.length).fill(0)];
    const matrix = Array.from({ length: dimension }, (_, row) =>
        Array.from({ length: dimension }, (_, col) => padded[row * dimension + col]));
    return { values, padded, matrix };
}

function flattenRowMajor(matrix) {
    return matrix.flat();
}

async function animateEncoding(text, values, cipher) {
    const run = ++encodingRun;
    const readout = byId("enc-encoding-readout");
    const source = byId("enc-text");
    const stages = [
        `Texto recibido · ${text}`,
        `Mapeo numérico · [${values.join(", ")}]`,
        `Valores cifrados · [${flattenRowMajor(cipher).join(", ")}]`
    ];
    readout.hidden = false;
    source.classList.remove("encode-source-active");
    void source.offsetWidth;
    source.classList.add("encode-source-active");
    setTimeout(() => source.classList.remove("encode-source-active"), 1150);
    if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
        readout.textContent = stages[stages.length - 1];
        return;
    }
    for (const stage of stages) {
        if (run !== encodingRun) return;
        readout.classList.remove("encoding-stage");
        void readout.offsetWidth;
        readout.textContent = stage;
        readout.setAttribute("aria-label", stage);
        readout.classList.add("encoding-stage");
        await new Promise((resolve) => setTimeout(resolve, 370));
    }
    if (run === encodingRun) readout.classList.add("encoding-complete");
}

function showProcess(processId, toggleId, cards) {
    const container = byId(processId);
    const toggle = byId(toggleId);
    const opening = container.hidden;
    if (opening) {
        cards.forEach((card, index) => {
            card.style.setProperty("--step-index", index);
            card.classList.remove("process-enter");
            void card.offsetWidth;
            card.classList.add("process-enter");
            card.querySelectorAll(".math-view").forEach(sweepMathView);
        });
        container.replaceChildren(...cards);
        container.hidden = false;
        toggle.textContent = "Ocultar proceso";
        toggle.setAttribute("aria-expanded", "true");
        if (window.MathJax && window.MathJax.typesetPromise) {
            window.MathJax.typesetPromise([container]).catch((error) => console.error("No se pudo representar la fórmula:", error));
        }
    } else {
        container.hidden = true;
        toggle.textContent = "🔍 Mostrar proceso paso a paso";
        toggle.setAttribute("aria-expanded", "false");
    }
}

function scrambleReveal(element, finalText, duration = 1720) {
    const token = String(Number(element.dataset.scrambleToken || 0) + 1);
    element.dataset.scrambleToken = token;
    element.setAttribute("aria-label", finalText);
    if (window.matchMedia("(prefers-reduced-motion: reduce)").matches || !finalText) {
        element.textContent = finalText;
        element.removeAttribute("aria-busy");
        element.classList.remove("scrambling");
        return;
    }

    // Resuelve de izquierda a derecha y reserva el final para el destello de cada carácter.
    const characters = Array.from(finalText);
    const resolutionDuration = duration - 420;
    const glyphs = characters.map((character) => {
        const glyph = document.createElement("span");
        glyph.className = "scramble-glyph";
        glyph.textContent = /\s/.test(character)
            ? character
            : SCRAMBLE_CHARACTERS[Math.floor(Math.random() * SCRAMBLE_CHARACTERS.length)];
        if (/\s/.test(character)) glyph.classList.add("scramble-space");
        else glyph.classList.add("scramble-pending");
        return glyph;
    });
    const locked = characters.map((character) => /\s/.test(character));
    element.replaceChildren(...glyphs);
    const startedAt = performance.now();
    element.setAttribute("aria-busy", "true");
    element.classList.add("scrambling");
    const animate = () => {
        if (element.dataset.scrambleToken !== token) return;
        const elapsed = performance.now() - startedAt;
        characters.forEach((character, index) => {
            if (locked[index]) return;
            if (elapsed >= ((index + 1) / characters.length) * resolutionDuration) {
                locked[index] = true;
                glyphs[index].textContent = character;
                glyphs[index].classList.remove("scramble-pending");
                glyphs[index].classList.add("scramble-locked");
                setTimeout(() => glyphs[index].classList.remove("scramble-locked"), 420);
            } else {
                glyphs[index].textContent = SCRAMBLE_CHARACTERS[Math.floor(Math.random() * SCRAMBLE_CHARACTERS.length)];
            }
        });
        if (elapsed >= duration) {
            element.textContent = finalText;
            element.removeAttribute("aria-busy");
            element.classList.remove("scrambling");
        } else {
            setTimeout(animate, 32);
        }
    };
    animate();
}

function createStep(title, content) {
    const card = document.createElement("article");
    card.className = "step-card";
    const heading = document.createElement("h3");
    heading.textContent = title;
    card.append(heading, content);
    return card;
}

function createTextElement(tag, className, text) {
    const element = document.createElement(tag);
    if (className) element.className = className;
    element.textContent = text;
    return element;
}

function createBadges(values, labels) {
    const container = document.createElement("div");
    container.className = "badges";
    values.forEach((value, index) => {
        const badge = document.createElement("span");
        badge.className = "badge";
        const label = labels[index];
        badge.textContent = `[${label} → ${value}]`;
        container.appendChild(badge);
    });
    return container;
}

async function encryptMessage() {
    animateButton(byId("encrypt-button"), "encrypt-action", 1250);
    const validKey = validateKeyMatrix("enc");
    if (!validKey) {
        showToast("La matriz clave no es válida. Revisa sus valores y su determinante.", "error");
        return;
    }
    const text = byId("enc-text").value;
    if (!text.length) {
        showToast("Escribe al menos un carácter antes de encriptar.", "error");
        return;
    }
    const dimension = validKey.matrix.length;
    const { values, padded, matrix: plainMatrix } = makeMessageMatrix(text, dimension);
    let cipherMatrix;
    try {
        cipherMatrix = multiplyMatrices(validKey.matrix, plainMatrix);
    } catch (error) {
        showToast(error.message, "error");
        return;
    }
    rememberEncryptionKey(validKey.matrix);
    const payload = {
        format: "matrix-cipher-lab",
        dimension,
        B_matrix: cipherMatrix,
        original_length: text.length,
        lowercase: Array.from(text, (character) => character !== " " && character === character.toLowerCase())
    };
    if (downloadUrl) URL.revokeObjectURL(downloadUrl);
    downloadUrl = URL.createObjectURL(new Blob([JSON.stringify(payload, null, 2)], { type: "application/json" }));
    byId("download-json").href = downloadUrl;
    byId("enc-results").hidden = false;
    byId("enc-results").classList.remove("result-arrive");
    void byId("enc-results").offsetWidth;
    byId("enc-results").classList.add("result-arrive");
    byId("enc-process").hidden = true;
    byId("enc-process-toggle").textContent = "🔍 Mostrar proceso paso a paso";
    byId("enc-process-toggle").setAttribute("aria-expanded", "false");
    byId("enc-encoding-readout").classList.remove("encoding-complete");
    byId("enc-results").scrollIntoView({ behavior: "smooth", block: "start" });
    await Promise.all([
        renderMath(byId("enc-final-matrix"), `B = ${matrixLatex(cipherMatrix)}`),
        animateEncoding(text, values, cipherMatrix)
    ]);
    sweepMathView(byId("enc-final-matrix"));

    const labels = Array.from(text, (character) => character === " " ? "␣" : character);
    const allLabels = [...labels, ...Array(dimension * dimension - labels.length).fill("relleno")];
    const stepOne = createStep("Paso 1 — Conversión de texto a números",
        createBadges(padded, allLabels.map((label, index) => index >= labels.length ? "0 (relleno)" : label)));
    const xMath = document.createElement("div");
    xMath.className = "math-view";
    xMath.innerHTML = `\\[X = ${matrixLatex(plainMatrix)}\\]`;
    const stepTwoBody = document.createElement("div");
    stepTwoBody.append(xMath, createTextElement("p", "", "Los caracteres se colocan por filas. Las posiciones vacías se completan con 0 hasta formar una matriz n × n."));
    const stepTwo = createStep("Paso 2 — Construcción de la matriz X", stepTwoBody);
    const multiplyMath = document.createElement("div");
    multiplyMath.className = "math-view";
    multiplyMath.innerHTML = `\\[B = A \\times X = ${matrixLatex(validKey.matrix)} \\times ${matrixLatex(plainMatrix)}\\]`;
    const firstCalc = formatDotProduct(validKey.matrix[0], plainMatrix.map((row) => row[0]));
    const stepThreeBody = document.createElement("div");
    stepThreeBody.append(
        multiplyMath,
        createTextElement("p", "formula-note", `Cada celda de B es el producto punto de una fila de A y una columna de X. Por ejemplo: B₁₁ = ${firstCalc} = ${cipherMatrix[0][0]}.`)
    );
    const stepThree = createStep("Paso 3 — Operación matricial", stepThreeBody);
    const resultBody = document.createElement("div");
    resultBody.className = "math-view";
    resultBody.innerHTML = `\\[B = ${matrixLatex(cipherMatrix)}\\]`;
    const stepFour = createStep("Paso 4 — Resultado final", resultBody);
    byId("enc-process-toggle").onclick = () => showProcess("enc-process", "enc-process-toggle", [stepOne, stepTwo, stepThree, stepFour]);
}

function validatePayload(payload) {
    if (!payload || !Number.isInteger(payload.dimension) || payload.dimension < 3 || payload.dimension > MAX_DIMENSION) {
        return { valid: false, error: "El archivo debe indicar una dimensión entre 3 y 6." };
    }
    const dimension = payload.dimension;
    if (!Array.isArray(payload.B_matrix) || payload.B_matrix.length !== dimension ||
        payload.B_matrix.some((row) => !Array.isArray(row) || row.length !== dimension ||
            row.some((value) => !Number.isSafeInteger(value)))) {
        return { valid: false, error: "La matriz B del JSON debe ser cuadrada y contener solo enteros." };
    }
    if (payload.original_length !== undefined &&
        (!Number.isInteger(payload.original_length) || payload.original_length < 0 || payload.original_length > dimension ** 2)) {
        return { valid: false, error: "La longitud original indicada en el JSON no es válida." };
    }
    if (payload.lowercase !== undefined &&
        (!Array.isArray(payload.lowercase) || payload.lowercase.length !== payload.original_length ||
            payload.lowercase.some((value) => typeof value !== "boolean"))) {
        return { valid: false, error: "Los metadatos de mayúsculas del JSON no son válidos." };
    }
    return { valid: true, dimension, matrix: payload.B_matrix };
}

function setFileStatus(message, success) {
    const status = byId("dec-file-status");
    status.className = `inline-status ${success ? "status-success" : "status-error"}`;
    status.textContent = message;
}

async function loadCipherFile(file) {
    if (!file) return;
    uploadedCipher = null;
    try {
        const payload = JSON.parse(await file.text());
        const validation = validatePayload(payload);
        if (!validation.valid) {
            setFileStatus(`✕ ${validation.error}`, false);
            showToast(validation.error, "error");
            return;
        }
        if (getDimension("dec") !== validation.dimension) {
            setDimension("dec", validation.dimension);
        }
        buildCipherEditor(validation.matrix);
        uploadedCipher = {
            dimension: validation.dimension,
            matrix: validation.matrix,
            originalLength: payload.original_length,
            lowercase: payload.lowercase
        };
        setFileStatus(`✓ JSON válido · matriz ${validation.dimension} × ${validation.dimension}`, true);
        showToast(`JSON cifrado cargado · matriz ${validation.dimension} × ${validation.dimension}.`, "success");
    } catch (error) {
        setFileStatus("✕ No se pudo leer el archivo. Comprueba que sea un JSON válido.", false);
        console.error("Error al leer el archivo cifrado:", error);
        showToast("No se pudo leer el archivo JSON cifrado.", "error");
    }
}

function reconstructMessage(values, metadata) {
    const text = [];
    values.forEach((value, index) => {
        if (value === 0) text.push(" ");
        else {
            const letter = NUM_TO_CHAR[value];
            text.push(metadata && metadata[index] ? letter.toLowerCase() : letter);
        }
    });
    return text.join("");
}

// Solo se corrigen residuos de coma flotante dentro de tolerancia; el resto se rechaza.
function decodedNumbers(inverse, cipher) {
    const floating = multiplyMatrices(inverse, cipher);
    const rounded = [];
    for (let row = 0; row < floating.length; row += 1) {
        const roundedRow = [];
        for (let col = 0; col < floating[row].length; col += 1) {
            const value = floating[row][col];
            const integer = Math.round(value);
            if (!Number.isFinite(value) || Math.abs(value - integer) > 1e-7 || integer < 0 || integer > 27) {
                throw new Error("La clave no coincide o la matriz cifrada está dañada: se obtuvo un valor no entero fuera del rango 0–27.");
            }
            roundedRow.push(integer);
        }
        rounded.push(roundedRow);
    }
    return rounded;
}

async function decryptMessage() {
    animateButton(byId("decrypt-button"), "decrypt-action", 1250);
    const validKey = validateKeyMatrix("dec");
    if (!validKey) {
        showToast("La matriz clave no es válida. Revisa sus valores y su determinante.", "error");
        return;
    }
    const dimension = validKey.matrix.length;
    let cipher;
    let originalLength;
    let lowercase;
    if (uploadedCipher) {
        if (uploadedCipher.dimension !== dimension) {
            showToast(`La clave es ${dimension} × ${dimension}, pero el JSON contiene una matriz ${uploadedCipher.dimension} × ${uploadedCipher.dimension}.`, "error");
            return;
        }
        cipher = uploadedCipher.matrix;
        originalLength = uploadedCipher.originalLength;
        lowercase = uploadedCipher.lowercase;
    } else {
        const manual = readCipherMatrix();
        if (!manual.valid) {
            showToast(manual.error, "error");
            return;
        }
        cipher = manual.matrix;
    }

    let inverse;
    let recovered;
    try {
        inverse = inverseMatrix(validKey.matrix);
        recovered = decodedNumbers(inverse, cipher);
    } catch (error) {
        showToast(error.message || "No fue posible descifrar los datos con esta clave.", "error");
        return;
    }
    const flat = flattenRowMajor(recovered);
    let values;
    if (Number.isInteger(originalLength)) values = flat.slice(0, originalLength);
    else {
        values = [...flat];
        while (values.length && values[values.length - 1] === 0) values.pop();
    }
    lastDecryptedText = reconstructMessage(values, lowercase);
    byId("dec-results").hidden = false;
    byId("dec-results").classList.remove("result-arrive");
    void byId("dec-results").offsetWidth;
    byId("dec-results").classList.add("result-arrive");
    scrambleReveal(byId("dec-final-text"), lastDecryptedText || "(mensaje vacío)");
    scrambleReveal(byId("dec-result-note"), `Valores recuperados: [${values.join(", ")}]`);
    byId("dec-process").hidden = true;
    byId("dec-process-toggle").textContent = "🔍 Mostrar proceso paso a paso";
    byId("dec-process-toggle").setAttribute("aria-expanded", "false");
    byId("dec-copy-status").textContent = "";

    const chars = values.map((value) => value === 0 ? "␣" : NUM_TO_CHAR[value]);
    const stepOne = createStep("Paso 1 — Conversión de texto a números", createBadges(values, chars));
    const xMath = document.createElement("div");
    xMath.className = "math-view";
    xMath.innerHTML = `\\[X = ${matrixLatex(recovered)}\\]`;
    const stepTwo = createStep("Paso 2 — Matriz recuperada X", xMath);
    const inverseMath = document.createElement("div");
    inverseMath.className = "math-view";
    inverseMath.innerHTML = `\\[\\det(A) = ${validKey.determinant.toString()}, \\qquad A^{-1} = ${matrixLatex(inverse, true)}\\]`;
    const operationMath = document.createElement("div");
    operationMath.className = "math-view";
    operationMath.innerHTML = `\\[X = A^{-1} \\times B = ${matrixLatex(inverse, true)} \\times ${matrixLatex(cipher)}\\]`;
    const firstCalc = formatDotProduct(
        inverse[0].map((value) => Number(value.toFixed(4))),
        cipher.map((row) => row[0])
    );
    const stepThreeBody = document.createElement("div");
    stepThreeBody.append(
        inverseMath,
        operationMath,
        createTextElement("p", "formula-note", `La inversa deshace la transformación. La primera posición se calcula con la fila 1 de A⁻¹ por la columna 1 de B: X₁₁ = ${firstCalc} ≈ ${recovered[0][0]}.`)
    );
    const stepThree = createStep("Paso 3 — Inversa y operación matricial", stepThreeBody);
    const stepFour = createStep("Paso 4 — Traducción de vuelta a letras",
        createTextElement("p", "result-text", lastDecryptedText || "(mensaje vacío)"));
    byId("dec-process-toggle").onclick = () => showProcess("dec-process", "dec-process-toggle", [stepOne, stepTwo, stepThree, stepFour]);
    byId("dec-results").scrollIntoView({ behavior: "smooth", block: "start" });
}

function showToast(message, type = "info", duration = 4200) {
    const toast = document.createElement("div");
    toast.className = `toast ${type}`;
    toast.setAttribute("role", type === "error" ? "alert" : "status");
    const icon = document.createElement("span");
    icon.className = "toast-icon";
    icon.setAttribute("aria-hidden", "true");
    icon.textContent = type === "error" ? "✕" : type === "success" ? "✓" : "ⓘ";
    const text = document.createElement("span");
    text.textContent = message;
    toast.append(icon, text);
    byId("toast-region").appendChild(toast);
    setTimeout(() => {
        toast.classList.add("toast-leave");
        toast.addEventListener("animationend", () => toast.remove(), { once: true });
        setTimeout(() => toast.remove(), 280);
    }, duration);
}

function isValidSavedKey(saved) {
    if (!saved || !Number.isInteger(saved.dimension) || saved.dimension < 3 || saved.dimension > MAX_DIMENSION) return false;
    if (!Array.isArray(saved.matrix) || saved.matrix.length !== saved.dimension ||
        saved.matrix.some((row) => !Array.isArray(row) || row.length !== saved.dimension ||
            row.some((value) => !Number.isSafeInteger(value)))) return false;
    return determinantInteger(saved.matrix) !== 0n;
}

function updateLastKeyControl() {
    const button = byId("use-last-key");
    const help = byId("last-key-help");
    button.disabled = !lastEncryptionKey;
    button.title = lastEncryptionKey
        ? `Clave ${lastEncryptionKey.dimension} × ${lastEncryptionKey.dimension} disponible`
        : "Se activa después de encriptar un mensaje.";
    help.textContent = lastEncryptionKey
        ? `Clave ${lastEncryptionKey.dimension} × ${lastEncryptionKey.dimension} lista para reutilizar en esta pestaña.`
        : "Se activará después de encriptar un mensaje.";
}

function rememberEncryptionKey(matrix) {
    lastEncryptionKey = {
        dimension: matrix.length,
        matrix: matrix.map((row) => [...row])
    };
    updateLastKeyControl();
    try {
        sessionStorage.setItem(LAST_KEY_STORAGE, JSON.stringify(lastEncryptionKey));
    } catch (error) {
        console.error("No se pudo guardar la clave en sessionStorage:", error);
        showToast("La clave se puede reutilizar en esta página, pero el navegador no permitió guardarla para la pestaña.", "error");
    }
}

function restoreEncryptionKey() {
    let serialized;
    try {
        serialized = sessionStorage.getItem(LAST_KEY_STORAGE);
    } catch (error) {
        console.error("No se pudo acceder a sessionStorage:", error);
        showToast("No se pudo leer la clave guardada en esta pestaña.", "error");
        return;
    }
    if (!serialized) return;

    let saved;
    try {
        saved = JSON.parse(serialized);
    } catch (error) {
        console.error("La clave guardada no contiene JSON válido:", error);
        showToast("La última clave guardada está dañada; vuelve a encriptar para reemplazarla.", "error");
        return;
    }
    if (!isValidSavedKey(saved)) {
        showToast("La última clave guardada no es válida y no se puede reutilizar.", "error");
        return;
    }
    lastEncryptionKey = { dimension: saved.dimension, matrix: saved.matrix };
    updateLastKeyControl();
}

function useLastEncryptionKey() {
    if (!lastEncryptionKey) return;
    animateButton(byId("use-last-key"), "energy-transfer", 1050);
    if (getDimension("dec") !== lastEncryptionKey.dimension) {
        setDimension("dec", lastEncryptionKey.dimension);
    }
    fillMatrixEditor("dec", lastEncryptionKey.matrix, true);
    showToast("Última clave de encriptado cargada y validada.", "success");
}

function populateAlphabet() {
    const grid = byId("alphabet-grid");
    Array.from(ALPHABET).forEach((character, index) => {
        const cell = document.createElement("div");
        cell.className = "alphabet-cell";
        cell.innerHTML = `<b>${character}</b>${index + 1}`;
        grid.appendChild(cell);
    });
    const space = document.createElement("div");
    space.className = "alphabet-cell";
    space.innerHTML = "<b>␣</b>0";
    grid.appendChild(space);
}

byId("brand-home").addEventListener("click", (event) => {
    event.preventDefault();
    showScreen("home");
});
byId("home-button").addEventListener("click", () => showScreen("home"));
byId("switch-button").addEventListener("click", () => {
    showScreen(byId("encrypt-screen").hidden ? "encrypt" : "decrypt");
});
document.querySelectorAll("[data-screen]").forEach((button) => {
    button.addEventListener("click", () => showScreen(button.dataset.screen));
});
["enc", "dec"].forEach((prefix) => {
    byId(`${prefix}-dim`).addEventListener("change", () => buildMatrixEditor(prefix));
});
byId("enc-random").addEventListener("click", () => randomInvertibleMatrix("enc"));
byId("use-last-key").addEventListener("click", useLastEncryptionKey);
byId("enc-text").addEventListener("input", (event) => {
    const result = sanitizeMessage(event.target.value);
    const limit = getDimension("enc") ** 2;
    event.target.value = result.value.slice(0, limit);
    updateMessageCounter(result.rejected || result.value.length > limit);
});
byId("encrypt-button").addEventListener("click", encryptMessage);
byId("decrypt-button").addEventListener("click", decryptMessage);
byId("dec-file").addEventListener("change", (event) => loadCipherFile(event.target.files[0]));
byId("copy-result").addEventListener("click", async () => {
    const button = byId("copy-result");
    try {
        await navigator.clipboard.writeText(lastDecryptedText);
        button.textContent = "✓ ¡Copiado!";
        button.classList.add("copied");
        clearTimeout(copyResetTimer);
        copyResetTimer = setTimeout(() => {
            button.textContent = "⧉ Copiar resultado";
            button.classList.remove("copied");
        }, 1800);
        byId("dec-copy-status").className = "inline-status status-success";
        byId("dec-copy-status").textContent = "✓ Mensaje copiado al portapapeles.";
        showToast("Mensaje copiado al portapapeles.", "success");
    } catch (error) {
        byId("dec-copy-status").className = "inline-status status-error";
        byId("dec-copy-status").textContent = "No se pudo acceder al portapapeles. Selecciona y copia el mensaje manualmente.";
        showToast("No se pudo copiar. Selecciona el mensaje y cópialo manualmente.", "error");
    }
});

document.addEventListener("pointerdown", (event) => {
    const target = event.target instanceof Element
        ? event.target.closest("button:not(:disabled), a.button")
        : null;
    if (!target) return;
    const bounds = target.getBoundingClientRect();
    target.style.setProperty("--ripple-x", `${event.clientX - bounds.left}px`);
    target.style.setProperty("--ripple-y", `${event.clientY - bounds.top}px`);
    target.classList.remove("ripple-active");
    void target.offsetWidth;
    target.classList.add("ripple-active");
    clearTimeout(rippleTimers.get(target));
    rippleTimers.set(target, setTimeout(() => target.classList.remove("ripple-active"), 650));
});

window.addEventListener("load", () => {
    if (window.MathJax && window.MathJax.typesetPromise) {
        window.MathJax.typesetPromise(Array.from(document.querySelectorAll(".math-view")))
            .catch((error) => console.error("No se pudieron representar las fórmulas:", error));
    }
});

buildMatrixEditor("enc");
buildMatrixEditor("dec");
populateAlphabet();
restoreEncryptionKey();
showScreen("home");

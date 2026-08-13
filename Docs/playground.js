document.addEventListener("DOMContentLoaded", () => {
  const root = document.querySelector("[data-triptych-playground]");
  if (!root) return;

  const examples = {
    Decimal: [
      ["Positive", "1.5"],
      ["Negative", "-0.15"],
      ["Invalid fraction", "1.x"],
    ],
    Duration: [
      ["Several units", "1d2h30m"],
      ["Negative", "-4s200ms"],
      ["Missing component", "-"],
    ],
    Datetime: [
      ["UTC with millis", "2024-01-15T10:30:45.123Z"],
      ["Offset", "2024-01-15T10:30:45+0530"],
      ["Invalid date", "2024-02-30T00:00:00Z"],
    ],
    IPv4: [
      ["Address", "192.168.1.100"],
      ["CIDR network", "8.8.8.8/24"],
      ["Invalid octet", "256.0.0.1"],
    ],
    IPv6: [
      ["Compressed", "2001:db8::1"],
      ["CIDR network", "::1/128"],
      ["Invalid prefix", "::1/129"],
    ],
  };

  root.innerHTML = `
    <div class="tp-playground">
      <div class="tp-format-tabs" role="tablist" aria-label="Cedar format"></div>
      <form class="tp-controls">
        <label class="tp-input-control">
          <span>Input</span>
          <input name="input" type="text" autocomplete="off" spellcheck="false">
        </label>
        <label class="tp-example-control">
          <span>Example</span>
          <select name="example"></select>
        </label>
        <button type="submit">Parse</button>
      </form>
      <p class="tp-message" role="status" aria-live="polite"></p>
      <div class="tp-results" hidden>
        <section class="tp-validation" aria-label="Validation">
          <div><span>Well-formed</span><strong data-result="wellFormed"></strong></div>
          <div><span>Semantic constraints</span><strong data-result="semanticConstraints"></strong></div>
          <div><span>Valid</span><strong data-result="valid"></strong></div>
          <div><span>Parsers agree</span><strong data-result="agree"></strong></div>
        </section>
        <section class="tp-output-comparison" aria-label="Parser results">
          <div>
            <span>Generated parser</span>
            <code data-result="generatedResult"></code>
          </div>
          <div>
            <span>Checked Cedar parser</span>
            <code data-result="cedarResult"></code>
          </div>
        </section>
        <section class="tp-captures">
          <h2>Decoded fields</h2>
          <div class="tp-capture-table"></div>
        </section>
      </div>
    </div>`;

  const tabs = root.querySelector(".tp-format-tabs");
  const form = root.querySelector("form");
  const input = form.elements.input;
  const exampleSelect = form.elements.example;
  const submit = form.querySelector("button");
  const message = root.querySelector(".tp-message");
  const results = root.querySelector(".tp-results");
  const captureTable = root.querySelector(".tp-capture-table");
  let format = "Decimal";
  let requestNumber = 0;

  function setMessage(text, kind = "") {
    message.textContent = text;
    message.dataset.kind = kind;
  }

  function setBoolean(name, result) {
    const element = root.querySelector(`[data-result="${name}"]`);
    element.className = "";
    if (result === null) {
      element.textContent = "not separate";
      element.classList.add("tp-na");
    } else if (result) {
      element.textContent = "yes";
      element.classList.add("tp-pass");
    } else {
      element.textContent = "no";
      element.classList.add("tp-fail");
    }
  }

  function setParserResult(name, result) {
    const element = root.querySelector(`[data-result="${name}"]`);
    element.textContent = result ?? "rejected";
    element.classList.toggle("tp-rejected", result === null);
  }

  function renderFields(fields) {
    captureTable.replaceChildren();
    if (fields.length === 0) {
      const empty = document.createElement("p");
      empty.className = "tp-empty";
      empty.textContent = "No complete grammar match.";
      captureTable.append(empty);
      return;
    }

    const table = document.createElement("table");
    const body = document.createElement("tbody");
    fields.forEach((field) => {
      const row = document.createElement("tr");
      const name = document.createElement("th");
      const text = document.createElement("td");
      name.scope = "row";
      name.textContent = field.name;
      text.textContent = field.present ? (field.text || '""') : "absent";
      if (!field.present) text.classList.add("tp-absent");
      row.append(name, text);
      body.append(row);
    });
    table.append(body);
    captureTable.append(table);
  }

  function render(data) {
    setBoolean("wellFormed", data.wellFormed);
    setBoolean("semanticConstraints", data.semanticConstraints);
    setBoolean("valid", data.valid);
    setBoolean("agree", data.agree);
    setParserResult("generatedResult", data.generatedResult);
    setParserResult("cedarResult", data.cedarResult);
    renderFields(data.fields);
    results.hidden = false;
  }

  async function run() {
    const currentRequest = ++requestNumber;
    submit.disabled = true;
    setMessage("Running Lean parser...", "pending");
    try {
      const response = await fetch("/api/playground", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ format, input: input.value }),
      });
      const data = await response.json();
      if (!response.ok) throw new Error(data.error || "Parser request failed");
      if (currentRequest !== requestNumber) return;
      render(data);
      setMessage("Parsed by the generated Lean parser and checked Cedar parser.", "success");
    } catch (error) {
      if (currentRequest !== requestNumber) return;
      results.hidden = true;
      setMessage(error.message || "Playground backend is unavailable.", "error");
    } finally {
      if (currentRequest === requestNumber) submit.disabled = false;
    }
  }

  function updateExamples(shouldRun = true) {
    exampleSelect.replaceChildren();
    examples[format].forEach(([label, text], index) => {
      const option = document.createElement("option");
      option.value = String(index);
      option.textContent = label;
      exampleSelect.append(option);
    });
    input.value = examples[format][0][1];
    if (shouldRun) run();
  }

  Object.keys(examples).forEach((name) => {
    const button = document.createElement("button");
    button.type = "button";
    button.role = "tab";
    button.textContent = name;
    button.setAttribute("aria-selected", String(name === format));
    button.addEventListener("click", () => {
      format = name;
      tabs.querySelectorAll("button").forEach((tab) => {
        tab.setAttribute("aria-selected", String(tab === button));
      });
      updateExamples();
    });
    tabs.append(button);
  });

  exampleSelect.addEventListener("change", () => {
    input.value = examples[format][Number(exampleSelect.value)][1];
    run();
  });
  form.addEventListener("submit", (event) => {
    event.preventDefault();
    run();
  });

  updateExamples(false);
  run();
});

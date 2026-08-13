document.addEventListener("DOMContentLoaded", () => {
  const root = document.querySelector("[data-triptych-demo]");
  if (!root) return;

  const formats = ["Decimal", "Duration", "Datetime", "IPv4", "IPv6"];
  const artifacts = [
    ["Grammar", (format) => `Inputs/${format}.lean`],
    ["Readable spec", (format) => `Outputs/${format}/spec.lean`],
    ["Parser", (format) => `Outputs/${format}/parser.lean`],
    ["Proofs", (format) => `Outputs/${format}/soundness.lean`],
  ];
  const params = new URLSearchParams(window.location.search);
  const base = new URL(
    params.get("lean4web") || "https://live.lean-lang.org/",
    window.location.href,
  );
  if (!base.pathname.endsWith("/")) base.pathname += "/";
  const project = params.get("lean4webProject") || "lean-v4.31.0";
  const sources = new URL(
    params.get("sourceBase") ||
      "https://raw.githubusercontent.com/cruisesong7/triptych/main/cedar-examples/",
    window.location.href,
  );

  root.innerHTML = `
    <div class="tp-demo">
      <div class="tp-demo-toolbar">
        <div class="tp-demo-tabs" role="tablist" aria-label="Cedar format"></div>
        <a class="tp-demo-new" target="_blank" rel="noopener noreferrer">New grammar</a>
        <a class="tp-demo-open" target="_blank" rel="noopener noreferrer">Open in new tab</a>
      </div>
      <div class="tp-demo-filebar">
        <label>
          <span>File</span>
          <select aria-label="Cedar artifact"></select>
        </label>
        <code class="tp-demo-path"></code>
      </div>
      <div class="tp-demo-frame">
        <iframe
          title="Lean4web editor for the Triptych Cedar examples"
          allow="clipboard-read; clipboard-write"
        ></iframe>
      </div>
      <p class="tp-demo-note">
        Source is loaded from Triptych's main branch. CI checks it in the complete Lake project.
      </p>
    </div>`;

  const tabs = root.querySelector(".tp-demo-tabs");
  const select = root.querySelector("select");
  const path = root.querySelector(".tp-demo-path");
  const iframe = root.querySelector("iframe");
  const openLink = root.querySelector(".tp-demo-open");
  const newLink = root.querySelector(".tp-demo-new");
  let format = formats[0];

  function editorUrl(file) {
    const args = {
      project,
      url: new URL(file, sources).href,
    };
    const hash = Object.entries(args)
      .map(([key, value]) => `${key}=${encodeURIComponent(value).replace(/[()]/g, (char) =>
        `%${char.charCodeAt(0).toString(16)}`)}`)
      .join("&");
    const editor = new URL(base);
    editor.hash = hash;
    return editor.href;
  }

  function showFile() {
    const file = artifacts[Number(select.value)][1](format);
    const url = editorUrl(file);
    path.textContent = file;
    iframe.src = url;
    openLink.href = url;
  }

  function chooseFormat(button, name) {
    format = name;
    tabs.querySelectorAll("button").forEach((tab) => {
      tab.setAttribute("aria-selected", String(tab === button));
    });
    showFile();
  }

  artifacts.forEach(([name], index) => {
    const option = document.createElement("option");
    option.value = String(index);
    option.textContent = name;
    select.append(option);
  });

  formats.forEach((name, index) => {
    const button = document.createElement("button");
    button.type = "button";
    button.role = "tab";
    button.textContent = name;
    button.setAttribute("aria-selected", String(index === 0));
    button.addEventListener("click", () => chooseFormat(button, name));
    tabs.append(button);
    if (index === 0) chooseFormat(button, name);
  });

  select.addEventListener("change", showFile);
  newLink.href = editorUrl("LeanWeb/Starter.lean");
});

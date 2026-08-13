import { execFile } from "node:child_process";
import { createReadStream, existsSync } from "node:fs";
import { createServer } from "node:http";
import { dirname, extname, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";

const execFileAsync = promisify(execFile);
const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const options = {
  host: "127.0.0.1",
  port: 8002,
  site: resolve(repoRoot, "_site", "html-multi"),
  parser: resolve(repoRoot, "cedar-examples", ".lake", "build", "bin", "playground"),
};

for (let index = 2; index < process.argv.length; index += 2) {
  const key = process.argv[index]?.replace(/^--/, "");
  const rawValue = process.argv[index + 1];
  if (!(key in options) || rawValue === undefined) {
    throw new Error(`Unknown or incomplete option '${process.argv[index]}'`);
  }
  options[key] = key === "port" ? Number(rawValue) : rawValue;
}

options.site = resolve(options.site);
options.parser = resolve(options.parser);

const mimeTypes = {
  ".css": "text/css; charset=utf-8",
  ".html": "text/html; charset=utf-8",
  ".ico": "image/x-icon",
  ".js": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".png": "image/png",
  ".svg": "image/svg+xml",
  ".woff2": "font/woff2",
};

function sendJson(response, status, body) {
  response.writeHead(status, {
    "Content-Type": "application/json; charset=utf-8",
    "Cache-Control": "no-store",
  });
  response.end(JSON.stringify(body));
}

async function readJson(request) {
  let body = "";
  for await (const chunk of request) {
    body += chunk;
    if (body.length > 16384) throw new Error("Request is too large");
  }
  return JSON.parse(body);
}

async function parse(request, response) {
  if (!existsSync(options.parser)) {
    sendJson(response, 503, { error: "Lean playground executable has not been built." });
    return;
  }

  try {
    const body = await readJson(request);
    if (typeof body.format !== "string" || typeof body.input !== "string") {
      sendJson(response, 400, { error: "Expected string fields 'format' and 'input'." });
      return;
    }

    const { stdout } = await execFileAsync(options.parser, [body.format, body.input], {
      timeout: 15000,
      maxBuffer: 1024 * 1024,
    });
    sendJson(response, 200, JSON.parse(stdout));
  } catch (error) {
    const detail = error.stderr?.trim() || error.message || "Parser request failed.";
    sendJson(response, 500, { error: detail });
  }
}

function serveFile(request, response) {
  const url = new URL(request.url, `http://${request.headers.host || "localhost"}`);
  let pathname;
  try {
    pathname = decodeURIComponent(url.pathname);
  } catch {
    response.writeHead(400).end();
    return;
  }

  const relative = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
  const file = resolve(options.site, `.${relative}`);
  if (file !== options.site && !file.startsWith(`${options.site}${sep}`)) {
    response.writeHead(403).end();
    return;
  }
  if (!existsSync(file)) {
    response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
    response.end("Not found");
    return;
  }

  response.writeHead(200, {
    "Content-Type": mimeTypes[extname(file)] || "application/octet-stream",
    "Cache-Control": "no-cache",
  });
  createReadStream(file).pipe(response);
}

const server = createServer(async (request, response) => {
  if (
    (request.method === "GET" || request.method === "HEAD") &&
    (request.url === "/playground/" || request.url === "/lean-playground/")
  ) {
    response.writeHead(302, { Location: "/demo/" }).end();
  } else if (request.method === "POST" && request.url === "/api/playground") {
    await parse(request, response);
  } else if (request.method === "GET" || request.method === "HEAD") {
    serveFile(request, response);
  } else {
    response.writeHead(405, { Allow: "GET, HEAD, POST" }).end();
  }
});

server.listen(options.port, options.host, () => {
  console.log(`Triptych book: http://${options.host}:${options.port}/`);
});

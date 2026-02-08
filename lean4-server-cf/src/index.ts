import { Container, getContainer } from "@cloudflare/containers";

interface Env {
  LEAN_4_24_0: DurableObjectNamespace;
  LEAN_4_25_0: DurableObjectNamespace;
  LEAN_4_26_0: DurableObjectNamespace;
  LEAN_4_27_0: DurableObjectNamespace;
  LEAN_4_28_0_RC1: DurableObjectNamespace;
  MATHLIB_4_27_0: DurableObjectNamespace;
}

class BaseLeanContainer extends Container<Env> {
  defaultPort = 8000;
  sleepAfter = "10s";
  enableInternet = false;
}

export class Lean4v24Container extends BaseLeanContainer {}
export class Lean4v25Container extends BaseLeanContainer {}
export class Lean4v26Container extends BaseLeanContainer {}
export class Lean4v27Container extends BaseLeanContainer {}
export class Lean4v28rc1Container extends BaseLeanContainer {}

class BaseMathlib4Container extends Container<Env> {
  defaultPort = 8000;
  sleepAfter = "120s";
  enableInternet = false;
}

export class Mathlib4v27Container extends BaseMathlib4Container {}

const ROUTES: Record<string, { ns: keyof Env; rewrite: string; cold?: boolean }> = {
  "POST /lean-4-24-0":            { ns: "LEAN_4_24_0", rewrite: "/" },
  "GET /lean-4-24-0/health":      { ns: "LEAN_4_24_0", rewrite: "/health" },
  "POST /lean-4-24-0/cold":       { ns: "LEAN_4_24_0", rewrite: "/", cold: true },
  "POST /lean-4-25-0":            { ns: "LEAN_4_25_0", rewrite: "/" },
  "GET /lean-4-25-0/health":      { ns: "LEAN_4_25_0", rewrite: "/health" },
  "POST /lean-4-25-0/cold":       { ns: "LEAN_4_25_0", rewrite: "/", cold: true },
  "POST /lean-4-26-0":            { ns: "LEAN_4_26_0", rewrite: "/" },
  "GET /lean-4-26-0/health":      { ns: "LEAN_4_26_0", rewrite: "/health" },
  "POST /lean-4-26-0/cold":       { ns: "LEAN_4_26_0", rewrite: "/", cold: true },
  "POST /lean-4-27-0":            { ns: "LEAN_4_27_0", rewrite: "/" },
  "GET /lean-4-27-0/health":      { ns: "LEAN_4_27_0", rewrite: "/health" },
  "POST /lean-4-27-0/cold":       { ns: "LEAN_4_27_0", rewrite: "/", cold: true },
  "POST /lean-4-28-0-rc1":        { ns: "LEAN_4_28_0_RC1", rewrite: "/" },
  "GET /lean-4-28-0-rc1/health":  { ns: "LEAN_4_28_0_RC1", rewrite: "/health" },
  "POST /lean-4-28-0-rc1/cold":   { ns: "LEAN_4_28_0_RC1", rewrite: "/", cold: true },
  "POST /mathlib-4-27-0":           { ns: "MATHLIB_4_27_0", rewrite: "/" },
  "GET /mathlib-4-27-0/health":     { ns: "MATHLIB_4_27_0", rewrite: "/health" },
  "POST /mathlib-4-27-0/cold":      { ns: "MATHLIB_4_27_0", rewrite: "/", cold: true },
};

const CORS_HEADERS: Record<string, string> = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
  "Access-Control-Allow-Headers": "Content-Type",
  "Access-Control-Max-Age": "86400",
};

function withCors(response: Response): Response {
  const r = new Response(response.body, response);
  for (const [k, v] of Object.entries(CORS_HEADERS)) r.headers.set(k, v);
  return r;
}

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    if (request.method === "OPTIONS") {
      return new Response(null, { status: 204, headers: CORS_HEADERS });
    }

    const url = new URL(request.url);
    const key = `${request.method} ${url.pathname}`;
    const route = ROUTES[key];

    if (route) {
      const ns = env[route.ns] as DurableObjectNamespace;
      const id = route.cold ? ns.newUniqueId() : ns.idFromName("singleton");
      const stub = ns.get(id);
      const resp = await stub.fetch(new Request(new URL(route.rewrite, url), request));
      return withCors(resp);
    }

    return withCors(new Response("Not Found", { status: 404 }));
  },
};

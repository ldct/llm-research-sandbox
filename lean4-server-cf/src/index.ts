import { Container, getContainer } from "@cloudflare/containers";

interface Env {
  LEAN_4_24_0: DurableObjectNamespace;
  LEAN_4_25_0: DurableObjectNamespace;
  LEAN_4_26_0: DurableObjectNamespace;
  LEAN_4_27_0: DurableObjectNamespace;
  LEAN_4_28_0_RC1: DurableObjectNamespace;
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
};

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    const url = new URL(request.url);
    const key = `${request.method} ${url.pathname}`;
    const route = ROUTES[key];

    if (route) {
      const ns = env[route.ns] as DurableObjectNamespace;
      const id = route.cold ? ns.newUniqueId() : ns.idFromName("singleton");
      const stub = ns.get(id);
      return stub.fetch(new Request(new URL(route.rewrite, url), request));
    }

    return new Response("Not Found", { status: 404 });
  },
};

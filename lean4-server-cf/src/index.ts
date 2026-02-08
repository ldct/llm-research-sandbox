import { DurableObject } from "cloudflare:workers";

interface Env {
  LEAN_4_24_0: DurableObjectNamespace;
  LEAN_4_25_0: DurableObjectNamespace;
}

const CONTAINER_PORT = 8000;
const SLEEP_MS = 10 * 1000; // 10 seconds

class BaseLeanContainer extends DurableObject {
  private ensureRunning(): void {
    if (!this.ctx.container.running) {
      this.ctx.container.start({ enableInternet: false });
    }
  }

  override async containerStarted(): Promise<void> {
    await this.ctx.container.setInactivityTimeout(SLEEP_MS);
  }

  async fetch(request: Request): Promise<Response> {
    this.ensureRunning();
    const fetcher = this.ctx.container.getTcpPort(CONTAINER_PORT);
    const url = new URL(request.url);
    return fetcher.fetch(
      new Request(`http://container${url.pathname}${url.search}`, request),
    );
  }
}

export class Lean4v24Container extends BaseLeanContainer {}
export class Lean4v25Container extends BaseLeanContainer {}

const ROUTES: Record<string, { ns: keyof Env; rewrite: string }> = {
  "POST /lean-4-24-0":        { ns: "LEAN_4_24_0", rewrite: "/" },
  "GET /lean-4-24-0/health":  { ns: "LEAN_4_24_0", rewrite: "/health" },
  "POST /lean-4-25-0":        { ns: "LEAN_4_25_0", rewrite: "/" },
  "GET /lean-4-25-0/health":  { ns: "LEAN_4_25_0", rewrite: "/health" },
};

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    const url = new URL(request.url);
    const key = `${request.method} ${url.pathname}`;
    const route = ROUTES[key];

    if (route) {
      const ns = env[route.ns] as DurableObjectNamespace;
      const id = ns.idFromName("singleton");
      const stub = ns.get(id);
      return stub.fetch(new Request(new URL(route.rewrite, url), request));
    }

    return new Response("Not Found", { status: 404 });
  },
};

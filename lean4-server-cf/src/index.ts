import { DurableObject } from "cloudflare:workers";

interface Env {
  LEAN_CONTAINER: DurableObjectNamespace<LeanContainer>;
}

export class LeanContainer extends DurableObject<Env> {
  private static readonly CONTAINER_PORT = 8000;
  private static readonly SLEEP_MS = 2 * 60 * 1000; // 2 minutes

  private ensureRunning(): void {
    if (!this.ctx.container.running) {
      this.ctx.container.start({ enableInternet: false });
    }
  }

  override async containerStarted(): Promise<void> {
    await this.ctx.container.setInactivityTimeout(LeanContainer.SLEEP_MS);
  }

  async fetch(request: Request): Promise<Response> {
    this.ensureRunning();
    const containerFetcher = this.ctx.container.getTcpPort(LeanContainer.CONTAINER_PORT);
    const url = new URL(request.url);
    return containerFetcher.fetch(
      new Request(`http://container${url.pathname}${url.search}`, request),
    );
  }
}

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    const url = new URL(request.url);

    // Route POST / and GET /health to the container
    if (
      (url.pathname === "/" && request.method === "POST") ||
      (url.pathname === "/health" && request.method === "GET")
    ) {
      const id = env.LEAN_CONTAINER.idFromName("singleton");
      const stub = env.LEAN_CONTAINER.get(id);
      return stub.fetch(request);
    }

    return new Response("Not Found", { status: 404 });
  },
};

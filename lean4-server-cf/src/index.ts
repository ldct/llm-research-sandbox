export default {
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    const headers = { "Content-Type": "application/json" };

    if (url.pathname === "/health" && request.method === "GET") {
      return Response.json({ status: "ok", stub: true }, { headers });
    }

    if (url.pathname === "/" && request.method === "POST") {
      return Response.json(
        { ok: true, stdout: "2\n", stderr: "", exitCode: 0, elapsed: 0.0, stub: true },
        { headers },
      );
    }

    return new Response("Not Found", { status: 404 });
  },
};

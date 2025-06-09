# sse_server.py
from mcp.server.fastmcp import FastMCP

# Create an MCP server
mcp = FastMCP("SSE Demo Server")

# Add a simple tool
@mcp.tool()
def echo(message: str) -> str:
    """Echo a message back to the client"""
    return f"Server received: {message}"


if __name__ == "__main__":
    # Run with SSE transport (default)
    mcp.run(transport="sse")

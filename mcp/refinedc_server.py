from mcp.server.fastmcp import FastMCP
import subprocess
import os

mcp = FastMCP("RefinedC Server")

@mcp.tool()
def refinedc_check(filename: str) -> str:
    """
    Runs 'refinedc check' on the specified file and returns the command output.

    Args:
        filename: Name of the file to check with refinedc

    Returns:
        The combined stdout and stderr from running the command
    """

    # Set up the environment variable for the command
    env = os.environ.copy()
    env["command"] = f"refinedc check {filename}"

    # Run the script without shell=True
    result = subprocess.run(
        ["./run.sh"],
        env=env,
        capture_output=True,
        text=True
    )

    # Combine stdout and stderr in the response
    output = result.stdout
    if result.stderr:
        output += "\n" + result.stderr

    return output

if __name__ == "__main__":
    # Run with SSE transport (default)
    mcp.run(transport="sse")

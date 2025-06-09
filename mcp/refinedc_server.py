from mcp.server.fastmcp import FastMCP
import subprocess
import os
import uuid
from threading import Thread

mcp = FastMCP("RefinedC Server")

def run_check(filename: str, check_uuid: str):
    """
    Runs the check and writes results to a temp file
    """
    env = os.environ.copy()
    env["command"] = f"refinedc check {filename}"
    
    result = subprocess.run(
        ["./run.sh"],
        env=env,
        capture_output=True,
        text=True
    )

    output = result.stdout
    if result.stderr:
        output += "\n" + result.stderr

    with open(f"/tmp/tmp_{check_uuid}", "w") as f:
        f.write(output)

@mcp.tool()
def start_check(filename: str) -> str:
    """
    Starts a refinedc check on the specified file and returns a UUID to track it.

    Args:
        filename: Name of the file to check with refinedc

    Returns:
        UUID string to use for getting results
    """
    check_uuid = str(uuid.uuid4())
    
    # Start check in background thread
    Thread(target=run_check, args=(filename, check_uuid)).start()
    
    return check_uuid

@mcp.tool()
def get_check_result(check_uuid: str) -> str:
    """
    Gets the result of a check by UUID.

    Args:
        check_uuid: UUID returned from start_check

    Returns:
        The check results if complete, or empty string if still running
    """
    try:
        with open(f"/tmp/tmp_{check_uuid}", "r") as f:
            return f.read()
    except FileNotFoundError:
        return "File not found"

if __name__ == "__main__":
    # Run with SSE transport (default)
    mcp.run(transport="sse")

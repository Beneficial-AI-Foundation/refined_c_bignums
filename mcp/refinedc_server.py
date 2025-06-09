from mcp.server.fastmcp import FastMCP
import subprocess
import os
import uuid

mcp = FastMCP("RefinedC Server")

# Store running processes
processes = {}

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
    output_file = f"/tmp/tmp_{check_uuid}"
    
    env = os.environ.copy()
    env["command"] = f"refinedc check {filename}"
    env["TTY"] = "false"
    
    # Start process asynchronously
    with open(output_file, 'w') as f:
        proc = subprocess.Popen(
            ["./run.sh"],
            env=env,
            stdout=f,
            stderr=subprocess.STDOUT,
            text=True
        )
    
    # Store process object
    processes[check_uuid] = proc
    
    return check_uuid

@mcp.tool()
def get_check_result(check_uuid: str) -> str:
    """
    Gets the result of a check by UUID.

    Args:
        check_uuid: UUID returned from start_check

    Returns:
        The check results if complete, or status message if still running
    """
    if check_uuid not in processes:
        return "Unknown check ID"
        
    proc = processes[check_uuid]
    if proc.poll() is None:
        return "Check still running"
        
    # Process finished
    try:
        with open(f"/tmp/tmp_{check_uuid}", "r") as f:
            result = f.read()
        return result
    except FileNotFoundError:
        return "Output file not found"

@mcp.tool()
def count_side_conditions(check_uuid: str) -> str:
    """
    Counts the number of unsolved side conditions in a check result.
    Note: Will return 0 if there are syntax/type errors that prevent reaching side condition checks.

    Args:
        check_uuid: UUID returned from start_check

    Returns:
        Number of unsolved side conditions found in the output
    """
    if check_uuid not in processes:
        return "Unknown check ID"
        
    proc = processes[check_uuid]
    if proc.poll() is None:
        return "Check still running"
        
    try:
        with open(f"/tmp/tmp_{check_uuid}", "r") as f:
            content = f.read()
            count = content.count("Cannot solve side condition")
            return str(count)
    except FileNotFoundError:
        return "Output file not found"

if __name__ == "__main__":
    mcp.run()

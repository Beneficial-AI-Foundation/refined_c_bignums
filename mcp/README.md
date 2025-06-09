# uv docker template

## Installation

### With uv

This repo uses [uv](https://github.com/astral-sh/uv) for packaging,

1. Install with `curl -LsSf https://astral.sh/uv/install.sh | sh`
1. Run scripts using `uv run`.
   The first time you call uv, it will download all the necessary dependencies.

### With docker

uv doesn't work well on machines that don't follow the Filesystem Hierarchy Standard (e.g. NixOS).
To run uv in this case, use the provided Dockerfile:

1. Build the image with `./build.sh`
1. Enter the container with `./run.sh`. If you have GPUs, instead use `./run.sh --gpus all`
1. To mount a results directory, use `./run.sh -v /absolute/host/path/to/results/:/results`
1. Then inside the container you can run `uv run ...` as before

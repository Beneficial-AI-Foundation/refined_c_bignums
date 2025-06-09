#!/usr/bin/env sh
if [ -z "$command" ]; then
	command=/bin/bash
fi
if [ -z "$TTY" ]; then
	TTY=true
fi
FISH_MOUNT=""
if [ -d "$HOME/.local/share/fish" ]; then
	FISH_MOUNT="-v $HOME/.local/share/fish:/home/ocaml/.local/share/fish"
fi
# --memory-swap is RAM+swap,
# so by setting it to the same value as --memory, we disable swap
docker run $([ "$TTY" = true ] && echo "-it") --rm \
	--memory=10g \
	--memory-swap=10g \
	--cpus=1 \
	$@ \
	-v $(pwd):/code \
	$FISH_MOUNT \
	$(cat docker_name) \
	sh -c "$command"

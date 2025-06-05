let
  nixpkgs = fetchTarball {
	url = "https://github.com/NixOS/nixpkgs/tarball/8f1b52b04f2cb6e5ead50bd28d76528a2f0380ef";
	sha256 = "sha256:0854a0169bh2rlfvrsibaqlmsql0dp3ycwq5z8178kdl7q9h6rrq";
	};
  pkgs = import nixpkgs { config = {}; overlays = []; };
in

pkgs.mkShellNoCC {
  packages = with pkgs; [
    mdformat
  ];
}

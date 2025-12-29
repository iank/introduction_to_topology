{
  description = "Introduction to Topology devshell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShell = pkgs.mkShell {
          name = "topology-devshell";

          packages = with pkgs; [
            elan
          ];

          shellHook = ''
            export PS1='\[\033[1;34m\][topology:\w]\$\[\033[0m\] '
          '';
        };
      }
    );
}

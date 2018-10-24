{ nixpkgs ? <nixpkgs> }:

let
  pkgs = import nixpkgs { };
in {
  yggdrasil = import ./default.nix { inherit pkgs; };
}

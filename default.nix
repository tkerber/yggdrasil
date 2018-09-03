{ pkgs ? import <nixpkgs> { } }:
pkgs.haskellPackages.callPackage ./yggdrasil.nix { }

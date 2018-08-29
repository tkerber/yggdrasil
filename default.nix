{ pkgs ? import <nixpkgs> { } }:
pkgs.haskellPackages.callPackage ./cabal.nix { }

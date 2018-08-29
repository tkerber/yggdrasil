{ mkDerivation, base, random, stdenv }:
mkDerivation {
  pname = "yggdrasil";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base random ];
  homepage = "https://git.drwx.org/phd/yggdrasil";
  description = "Executable specifications of composable security protocols";
  license = stdenv.lib.licenses.agpl3;
}

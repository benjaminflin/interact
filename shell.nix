{ pkgs ? import <nixpkgs> { } }:
let agda = (pkgs.agda.withPackages (p: [ p.standard-library ]));
in
pkgs.mkShell {
    buildInputs = [ agda ];

    shellHook = ''
        export AGDA=${agda.out}/bin/agda;
    '';
}
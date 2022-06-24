{
    description = "Interaction Trees in Agda";
    inputs.flake-utils.url = "github:numtide/flake-utils";
    outputs = { self, nixpkgs, flake-utils }:
        flake-utils.lib.eachDefaultSystem 
        (system:
            let 
            pkgs = nixpkgs.legacyPackages.${system};
            deriv = pkgs.stdenv.mkDerivation {
                name = "interact";
                src = ./.;
                buildInputs = [ (pkgs.agda.withPackages (p: [ p.standard-library ])) ];
            }; 
            in
            {
                devShell = import ./shell.nix { inherit pkgs; };
                app.default = {
                    type = "app";
                    program = deriv.out.interact;
                };
                defaultPackage = deriv;
            }
        );

}
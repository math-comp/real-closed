{withEmacs ? false,
 nixpkgs ? (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/650a295621b27c4ebe0fa64a63fd25323e64deb3.tar.gz";
  sha256 = "0rxjkfiq53ibz0rzggvnp341b6kgzgfr9x6q07m2my7ijlirs2da";
}),
coq-version ? "8.9",
mc ? fetchGit {url = "https://github.com/math-comp/math-comp"; ref = "master";},
print-env ? false
}:
let
  config.packageOverrides = pkgs:

        let coqPackagesV = (with pkgs;{
              "8.7" = coqPackages_8_7;
              "8.8" = coqPackages_8_8;
              "8.9" = coqPackages_8_9;
              "8.10" = coqPackages_8_10;
            }."${coq-version}");
        in

    with pkgs; {
      coqPackages =
        coqPackagesV.overrideScope' (self: super: {
          coq = super.coq;
          mathcompPkgs = if builtins.isString mc then (super.mathcompGen mc)
                         else super.mathcomp.mathcompGen (o: {
                           version = "1.9.0";
                           src = mc;
                         });
          mathcomp = self.mathcompPkgs.all;
          ssreflect = self.mathcompPkgs.ssreflect;
          mathcomp-ssreflect = self.mathcompPkgs.ssreflect;
          mathcomp-fingroup = self.mathcompPkgs.fingroup;
          mathcomp-algebra = self.mathcompPkgs.algebra;
          mathcomp-field = self.mathcompPkgs.field;
          mathcomp-solvable = self.mathcompPkgs.solvable;
          mathcomp-character = self.mathcompPkgs.character;
          mathcomp-ssreflect_1_9 = self.mathcompPkgs.ssreflect;
          mathcomp-fingroup_1_9 = self.mathcompPkgs.fingroup;
          mathcomp-algebra_1_9 = self.mathcompPkgs.algebra;
          mathcomp-field_1_9 = self.mathcompPkgs.field;
          mathcomp-solvable_1_9 = self.mathcompPkgs.solvable;
          mathcomp-character_1_9 = self.mathcompPkgs.character;
          mathcomp_1_9-bigenough = self.mathcomp-bigenough;
        });
      coq = coqPackagesV.coq;
      emacs = emacsWithPackages (epkgs:
        with epkgs.melpaStablePackages; [proof-general]);
    };
in
with import nixpkgs {inherit config;};
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with coqPackages;
    [mathcomp-ssreflect mathcomp-bigenough mathcomp-algebra mathcomp-field])
                ++ lib.optional withEmacs emacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}

{
  inputs = {
    nixpkgs = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixos-unstable";
    };
  };

  outputs = { self, nixpkgs }@inputs: {
    devShell.x86_64-linux =
      with import nixpkgs { system = "x86_64-linux"; };
      mkShell {
        buildInputs = [
          idris2
          vimPlugins.idris2-vim
        ];
      };
  };
}

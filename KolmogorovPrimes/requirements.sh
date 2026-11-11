#!/bin/bash

# 1. Crie o projeto em formato TOML (padrão moderno do Lake)
# lake +leanprover/lean4:stable new KolmogorovPrimes

# 2. Sincronize o seu lean-toolchain exatamente com o da branch main da complexitylib
curl -sL https://raw.githubusercontent.com/cslib-community/complexitylib/main/lean-toolchain -o lean-toolchain

# 3. Adicione a complexitylib ao final do seu lakefile.toml
cat << 'EOF' >> lakefile.toml

[[require]]
name = "complexitylib"
git = "https://github.com/cslib-community/complexitylib"
rev = "main"
EOF

# 4. Baixe o manifesto de dependências (puxa complexitylib, cslib e mathlib alinhadas)
lake update complexitylib

# 5. Baixe os binários (.olean) pré-compilados da Mathlib (economiza ~40 min de build)
lake exe cache get

# 6. Compile o projeto para validar o ambiente
lake build
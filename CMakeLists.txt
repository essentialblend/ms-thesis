cmake_minimum_required(VERSION 3.10)

# Specify project name and lang-compiler
project(ms-thesis NONE)

# Locate agda and setup flags
find_program(AGDA_EXEC agda REQUIRED)

# Custom add_custom_target
add_custom_target(
  check-agda 
  ALL
  COMMAND PowerShell -ExecutionPolicy Bypass -File 
    ${CMAKE_SOURCE_DIR}/verify-proofs.ps1
    integers/comm-ring/final-proof.agda
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)

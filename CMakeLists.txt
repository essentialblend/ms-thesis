cmake_minimum_required(VERSION 3.10)

# Specify project name and lang-compiler
project(ms-thesis NONE)

# Locate agda and setup flags
find_program(AGDA_EXEC agda REQUIRED)

# Version sanity-check

execute_process(
  COMMAND ${AGDA_EXEC} --version
  OUTPUT_VARIABLE AGDA_VER_LINE
)

string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+" AGDA_VERSION ${AGDA_VER_LINE})

if(AGDA_VERSION VERSION_LESS "2.7.0.1")
{
  message(FATAL_ERROR "Agda version ${AGDA_VERSION} found; requires >= 2.7.0.1")
}
endif()

# Custom add_custom_target
add_custom_target(
  check-agda 
  ALL
  COMMAND PowerShell -ExecutionPolicy Bypass -File 
    ${CMAKE_SOURCE_DIR}/verify-proofs.ps1
    integers/comm-ring/final-proof.agda
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)

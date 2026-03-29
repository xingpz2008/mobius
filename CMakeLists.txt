cmake_minimum_required(VERSION 3.12)
project(MobiusSEAL CXX)

# Require C++17 or higher for SEAL
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ==========================================
# 1. Find SEAL Library
# ==========================================
find_package(SEAL REQUIRED)

# ==========================================
# 2. Find OpenMP (Crucial for AWS multi-core acceleration)
# Made optional to maintain compatibility with default macOS Apple Clang
# ==========================================
find_package(OpenMP)
if(OpenMP_CXX_FOUND)
    message(STATUS "OpenMP found. Multi-threading acceleration enabled!")
else()
    message(WARNING "OpenMP not found! The program will run in single-thread mode. \n"
                    "For better performance on macOS, run: 'brew install libomp'")
endif()

# ==========================================
# 3. Find GMP Library (Compatible with macOS and Linux)
# ==========================================
find_path(GMP_INCLUDE_DIR NAMES gmp.h 
          PATHS /opt/homebrew/include /usr/include /usr/local/include)

find_library(GMP_LIBRARY NAMES gmp 
             PATHS /opt/homebrew/lib /usr/lib /usr/local/lib /usr/lib/x86_64-linux-gnu)

# Check if GMP is successfully found
if(GMP_INCLUDE_DIR AND GMP_LIBRARY)
    message(STATUS "Found GMP include: ${GMP_INCLUDE_DIR}")
    message(STATUS "Found GMP library: ${GMP_LIBRARY}")
else()
    message(FATAL_ERROR "GMP library not found! \n"
                        "macOS: 'brew install gmp'\n"
                        "Ubuntu/Debian: 'sudo apt-get install libgmp-dev'\n"
                        "Amazon Linux: 'sudo yum install gmp-devel'")
endif()

# ==========================================
# 4. Find Threads Library (Required for Linux network programming)
# ==========================================
find_package(Threads REQUIRED)

# ==========================================
# Target 2: Network node program for real environments
# ==========================================
add_executable(network_node network_node.cpp helper.cpp)
target_include_directories(network_node PRIVATE ${GMP_INCLUDE_DIR})

# Link SEAL, GMP, Threads, and conditionally link OpenMP
if(OpenMP_CXX_FOUND)
    target_link_libraries(network_node 
        SEAL::seal 
        ${GMP_LIBRARY} 
        Threads::Threads 
        OpenMP::OpenMP_CXX
    )
else()
    target_link_libraries(network_node 
        SEAL::seal 
        ${GMP_LIBRARY} 
        Threads::Threads
    )
endif()
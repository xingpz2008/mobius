cmake_minimum_required(VERSION 3.12)
project(MobiusSEAL CXX)

# SEAL 库要求使用 C++17 或以上标准
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 寻找系统上安装的 SEAL 库
find_package(SEAL REQUIRED)

find_path(GMP_INCLUDE_DIR NAMES gmp.h 
          PATHS /opt/homebrew/include /usr/local/include)

find_library(GMP_LIBRARY NAMES gmp 
             PATHS /opt/homebrew/lib /usr/local/lib)

# 检查是否成功找到 GMP
if(GMP_INCLUDE_DIR AND GMP_LIBRARY)
    message(STATUS "成功找到 GMP 头文件: ${GMP_INCLUDE_DIR}")
    message(STATUS "成功找到 GMP 库文件: ${GMP_LIBRARY}")
else()
    message(FATAL_ERROR "未找到 GMP 库！请确认是否已通过 brew install gmp 安装。")
endif()

# ==========================================
# 目标 1：单机版的模拟程序 (之前写的)
# ==========================================
add_executable(simulate_bs simulate_bs.cpp helper.cpp)
target_link_libraries(simulate_bs SEAL::seal)

# ==========================================
# 目标 2：真实网络环境的节点程序 (刚才写的)
# ==========================================
add_executable(network_node network_node.cpp helper.cpp)
target_include_directories(network_node PRIVATE ${GMP_INCLUDE_DIR})

# 将 SEAL 和 GMP 库链接到你的程序上
target_link_libraries(network_node SEAL::seal ${GMP_LIBRARY})
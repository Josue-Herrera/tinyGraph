cmake_minimum_required(VERSION 3.0.0)
set(TARGET_NAME Learning)

project(${TARGET_NAME})
set(CMAKE_CXX_STANDARD 20)

FILE(GLOB src src/*.cpp src/*.cc src/*.cxx )
FILE(GLOB includes inc/*.h inc/*.hpp inc/*.hxx)

add_executable(${TARGET_NAME} ${src} ${includes})
target_include_directories(${TARGET_NAME} PUBLIC ${includes} )

#set(eigen ${CMAKE_SOURCE_DIR}/../../Libraries/eigen)
#target_include_directories(${TARGET_NAME} PUBLIC ${eigen})



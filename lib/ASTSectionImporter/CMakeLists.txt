add_swift_host_library(swiftASTSectionImporter STATIC
  ASTSectionImporter.cpp
  LLVM_LINK_COMPONENTS core)
target_link_libraries(swiftASTSectionImporter PRIVATE
  swiftBasic)


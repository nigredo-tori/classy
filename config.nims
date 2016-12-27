import ./classy.nimble
import ospaths

# Tasks

proc createDirs() =
  mkDir binDir

task tests, "Run all tests":
  exec "nim test_classy"
  exec "nim example"

task test_classy, "Run classy API test":
  createDirs()
  switch("out", binDir / "test_classy".toExe)
  --run
  setCommand "c", "tests/test_classy.nim"

task example, "Run example":
  createDirs()
  switch("out", binDir / "example".toExe)
  --run
  setCommand "c", "example.nim"

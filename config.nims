# Tasks

task tests, "Run tests":
  selfExec "tests_private"
  selfExec "tests_api"

task test_api, "Run public API tests":
  --run
  setCommand "c", "tests/test_api.nim"

task test_private, "Run private tests":
  --run
  setCommand "c", "tests/test_private.nim"

task example, "Run example":
  --run
  setCommand "c", "example.nim"

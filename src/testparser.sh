#!/bin/bash

# this test script assumes you have full contents of release on the (project root)/release
# and java8 will invoke JRE 8.

cp parser_wip.js ../release/assets/disk0/tbas/basic.js
cd ../release
java8 -jar TSVM-Executable.jar > testlog.log

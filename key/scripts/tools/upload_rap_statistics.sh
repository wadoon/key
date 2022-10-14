#!/usr/bin/python3

import sys
import os
import re
import urllib
import json
import pprint
import requests


HOST="https://git.key-project.org/api/v4"
PROJECT_ID=58 # see https://git.key-project.org/key/key-stats/edit

# This is a secret given by JENKINS
# $DEPLOY_TOKEN

# PROVIDED BY JENKINS
# https://hudson.se.informatik.tu-darmstadt.de/env-vars.html/
# $BRANCH_NAME

TARGET_FOLDER="statistics/$BRANCH_NAME/$BUILD_NUMBER"
MESSAGE="auto-commit: Publish statistics for run $BUILD_DISPLAY_NAME in $JOB_NAME

Files are added in $TARGET_FOLDER
Goto Jenkins: $JOB_DISPLAY_URL
"

## Write Environment information
set > env.sh

## Statistic files
FUN_CSV=key.core/build/reports/runallproofs/runStatistics.csv
IF_CSV=key.core/build/reports/runallproofs/runStatistics_infflow.csv

curl --request POST \
     --form "branch=master" \
     --form "commit_message=$MESSAGE" \
     --form "start_branch=master" \
     \
     --form "actions[][action]=create" \
     --form "actions[][file_path]=$TARGET_FOLDER/env.sh" \
     --form "actions[][content]=<env.sh" \
     \
     --form "actions[][action]=create" \
     --form "actions[][file_path]=$TARGET_FOLDER/run_functional_stats.csv" \
     --form "actions[][content]=<$FUN_CSV" \
     \
     --form "actions[][action]=create" \
     --form "actions[][file_path]=$TARGET_FOLDER/run_infflow_stats.csv" \
     --form "actions[][content]=<$IF_CSV" \
     \
     --header "PRIVATE-TOKEN: $DEPLOY_TOKEN" \
     "$HOST/projects/$PROJECT_ID/repository/commits"


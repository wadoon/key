#!/usr/bin/python3

import sys
import os
import re
import urllib
import json
import pprint
import requests


HOST = "https://git.key-project.org/api/v4"
PROJECT_ID = 58 # see https://git.key-project.org/key/key-stats/edit
TOKEN = os.environ["DEPLOY_TOKEN"]

GIT_BRANCH=...

def upload_files(seq):
  # API
  # https://docs.gitlab.com/ee/api/commits.html#create-a-commit-with-multiple-files-and-actions
  # POST /projects/:id/repository/commits

  url = f"{HOST}/projects/{PROJECT_ID}/repository/files/{destination}"

  actions = []
  payload = {
    'branch' : 'main',
    'commit_message' : f"auto-commit: Run all proofs statistics from branch {GIT_BRANCH}",
    'actions': actions
  }

  for destination, local_filename in seq:
    with open(local_filename) as fh:
        content = fh.read()

    act = {
        'action':  'create', # any of create, delete, move, update, chmod
        "file_path": destination,
        "content": content,

    }

  resp = requests.post(checkUrl,data=json., headers={"Private-Token": TOKEN})
  if resp.status_code != 200:
      print(resp.content)
      sys.exit(0)

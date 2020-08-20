#!/usr/bin/python3
# Written by Alexander Weigl

import sys, os, re, fileinput, json

regex = re.compile(r'\[(?P<level>.*?)\] (?P<path>.*\/(?P<file>.*?)):(?P<line>\d+)(:\d+)?: (?P<msg>.*)')

# format https://docs.gitlab.com/ee/user/project/merge_requests/code_quality.html#code-quality-widget
#        https://github.com/codeclimate/platform/blob/master/spec/analyzers/SPEC.md#data-types

data = []

for line in fileinput.input():
    m = regex.match(line)
    if m:
        entry = {
            "type": "issue",
            "check_name": "Checkstyle",
            "severity": m.group('level'),
            "description": m.group('msg'),
            "fingerprint": id(m),
            "location": {
                "path": m.group('path')+"/"+m.group('file'), 
                "lines": { "begin": m.group('line') }
            }
        }
        data.add(entry)

json.dump(data, sys.stdout)

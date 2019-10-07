#! /usr/bin/python3

# ck is for "contact key"

import socket
import json
import sys

sys.argv.pop(0)

if len(sys.argv) < 1:
    print("At least command argument needed")
    exit(1)

if len(sys.argv) % 2 == 0:
    print("Need an odd number of arguments")
    exit(2)

command = { "command": sys.argv.pop(0) }

while len(sys.argv) > 0:
    k = sys.argv.pop(0)
    v = sys.argv.pop(0)
    command[k] = v

json = json.dumps(command)

print("command:  " + json);
    
with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
    s.connect(('localhost', 5533))
    s.sendall(json.encode('utf-8'))
    s.shutdown(1)
    data = s.recv(1024)

print("response: " + data.decode("utf-8"))

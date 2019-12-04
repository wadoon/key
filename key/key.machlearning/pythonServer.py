#!/usr/bin/python3
import socket
import random
import signal


PORT = 6767
TACTICS = ("AUTO", "SMT", "AUTO_NOSPLIT") # , "---unknown---")

# https://pymotw.com/2/socket/tcp.html
# Create a TCP/IP socket
sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

# Then bind() is used to associate the socket with the server address.
# In this case, the address is localhost

# Bind the socket to the port
server_address = ('localhost', PORT)
print('starting up on %s port %s' % server_address)
sock.bind(server_address)

# Calling listen() puts the socket into server mode,
# and accept() waits for an incoming connection.
# Listen for incoming connections
sock.listen(1)

def disconnect(signum, frame):
    global sock
    print('Closing connection')
    # tcflush(sys.stdin, TCIOFLUSH)
    sock.close()

# Set the signal handler and a 5-second alarm
signal.signal(signal.SIGTERM, disconnect)
signal.signal(signal.SIGINT, disconnect)

while True:
    # Wait for a connection
    print('waiting for a connection')
    connection, client_address = sock.accept()

    # accept() returns an open connection between the server and
    # client, along with the address of the client. The connection
    # is actually a different socket on another port (assigned by
    # the kernel). Data is read from the connection with recv() and
    # transmitted with sendall().

    try:
        print('connection from', client_address)

        # Receive the data in small chunks and retransmit it
        while True:
            data = connection.recv(1000000)
            print('received "%s"' % data)
            if data:
                index = random.randrange(len(TACTICS))
                tactic = TACTICS[index] + "\n"
                print('sending data back to the client', tactic)
                connection.sendall(tactic.encode())
            else:
                print('no more data from', client_address)
                break

    finally:
        # Clean up the connection
        connection.close()

def disconnect():
    print('Closing connection')

    connection.close()
    sock.close()

import atexit
atexit.register(disconnect)

from termios import tcflush, TCIOFLUSH
tcflush(sys.stdin, TCIOFLUSH)

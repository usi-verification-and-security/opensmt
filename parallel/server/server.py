import optparse
import asyncio

def c():
    return 3


@asyncio.coroutine
def handle_echo(reader, writer):
    data = yield from reader.read(100)
    message = data.decode()
    addr = writer.get_extra_info('peername')
    print("Received %r from %r" % (message, addr))

    message = eval(message)

    print("Send: %r" % message)
    writer.write(data)
    yield from writer.drain()

    print("Close the client socket")
    writer.close()


loop = asyncio.get_event_loop()

server_c = loop.run_until_complete(asyncio.start_server(handle_echo, '127.0.0.1', 5000))
server_w = loop.run_until_complete(asyncio.start_server(handle_echo, '127.0.0.1', 3000))

try:
    loop.run_forever()
except KeyboardInterrupt:
    pass
finally:
    server_w.close()
    server_c.close()
    loop.run_until_complete(
        asyncio.wait(
            (server_c.wait_closed(), server_w.wait_closed()),
            return_when=asyncio.ALL_COMPLETED
        )
    )
    loop.close()

if __name__ == '__main__':
    parser = optparse.OptionParser()
    parser.add_option('-c',
                      '--cport',
                      help='specify commands port number',
                      dest='cport',
                      type='int',
                      default=5000, )

    (options, args) = parser.parse_args()

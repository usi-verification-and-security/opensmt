import optparse
import asyncio

'''        data = yield from reader.read(100)
        message = data.decode()
        addr = writer.get_extra_info('peername')
        print("Received %r from %r" % (message, addr))

        message = eval(message)

        print("Send: %r" % message)
        writer.write(data)
        yield from writer.drain()

        print("Close the client socket")
        writer.close()'''


class Protocol(asyncio.streams.StreamReaderProtocol):
    def __init__(self, stream_reader, client_connected_cb=None, loop=None):
        super().__init__(loop=loop)
        self._stream_reader = stream_reader
        self._stream_writer = None
        self._client_connected_cb = client_connected_cb

    def connection_made(self, transport):
        self._stream_reader.set_transport(transport)
        if self._client_connected_cb is not None:
            self._stream_writer = StreamWriter(transport, self,
                                               self._stream_reader,
                                               self._loop)
            res = self._client_connected_cb(self._stream_reader,
                                            self._stream_writer)
            if coroutines.iscoroutine(res):
                self._loop.create_task(res)

    def connection_lost(self, exc):
        if exc is None:
            self._stream_reader.feed_eof()
        else:
            self._stream_reader.set_exception(exc)
        super().connection_lost(exc)

    def data_received(self, data):
        self._stream_reader.feed_data(data)

    def eof_received(self):
        self._stream_reader.feed_eof()


'''class Stream:
    def __init__(self, r, w):
        assert type(r) is asyncio.streams.StreamReader
        assert type(w) is asyncio.streams.StreamWriter
        self.r = r
        self.w = w

    @asyncio.coroutine
    def read(self, n=-1):
        return (yield from self.r.read(n)).decode()

    @asyncio.coroutine
    def write(self, data):
        self.w.write(data)
        yield from self.w.drain()

    def close(self):
        self.w.close()

class Server:
    def __init__(self, port, *, loop=None):
        if loop is None:
            loop = asyncio.get_event_loop()
        self.server = loop.run_until_complete(
            asyncio.start_server(asyncio.coroutine(lambda r, w: (yield from self.handle_message(Stream(r,w)))), '', port, loop=loop))

    @asyncio.coroutine
    def handle_message(self, s):
        print('S')

    def close(self):
        self.server.close()

    @asyncio.coroutine
    def wait_closed(self):
        yield from self.server.wait_closed()


class CommandServer(Server):
    def __init__(self, port=4000, *, loop=None):
        super().__init__(port, loop=loop)

    @asyncio.coroutine
    def handle_message(self, s):
        message = yield from s.read(100)
        print("C %r" % message)


class WorkerServer(Server):
    def __init__(self, port=3000, *, loop=None):
        super().__init__(port, loop=loop)

    @asyncio.coroutine
    def handle_message(self, s):
        message = yield from s.read(100)
        print("W %r" % message)'''


loop = asyncio.get_event_loop()

'''server_c = CommandServer()
server_w = WorkerServer()'''


class SimpleEchoProtocol(asyncio.Protocol):
    def connection_made(self, transport):
        """
        Called when a connection is made.
        The argument is the transport representing the pipe connection.
        To receive data, wait for data_received() calls.
        When the connection is closed, connection_lost() is called.
        """
        print("Connection received!")
        self.transport = transport

    def data_received(self, data):
        """
        Called when some data is received.
        The argument is a bytes object.
        """
        print(data)
        self.transport.write(b'echo:')
        self.transport.write(data)

    def connection_lost(self, exc):
        """
        Called when the connection is lost or closed.
        The argument is an exception object or None (the latter
        meaning a regular EOF is received or the connection was
        aborted or closed).
        """
        print("Connection lost! Closing server...")
        #server.close()

server = loop.run_until_complete(loop.create_server(SimpleEchoProtocol, '', 2222))
asyncio.start_server

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

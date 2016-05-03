# import server
import socket
import collections
import enum


# s=server.Socket()
# s.listen(('0.0.0.0', 3000))
#
# c=server.Socket()
# c.connect(('0.0.0.0', 3000))
#
#
# m=server.Message()
# m.header['a']='3'
# m.header['b']=4
# m.payload=b'yeee'
#
# dump1 = m.dump()
# c.write(dump1)
#
# d = s.accept()
# dump2 = d.read()
# m1=server.Message()
# m1.load(dump2)
#
# print(m.header==m1.header)
# print(m.payload==m1.payload)


# def keypaths(nested):
#     for key, value in nested.items():
#         if isinstance(value, collections.Mapping):
#             for subkey, subvalue in keypaths(value):
#                 yield [key] + subkey, subvalue
#         else:
#             yield [key], value
#
#
# example_dict = {'key1': 'value1',
#                 'key2': 'value2',
#                 'key3': {'key3a': 'value3a'},
#                 'key4': {'key4a': {'key4aa': 'value4aa',
#                                    'key4ab': 'value4ab',
#                                    'key4ac': 'value1'},
#                          'key4b': 'value4b'}
#                 }

# for keypath, value in keypaths(example_dict):
#     print(keypath, value)

# reverse_dict = {}
# for keypath, value in keypaths(example_dict):
#     reverse_dict.setdefault(value, []).append(keypath)
#
# print(reverse_dict['value4b'])



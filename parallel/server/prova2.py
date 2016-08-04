import net
so=net.Socket()
so.listen(("127.0.0.1",3000))
c=so.accept()
a=[]
for i in range(8):
 a.append(c.read())
 
for item in a:
 c.write(*item) 


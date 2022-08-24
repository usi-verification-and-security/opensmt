import sys
import os
import re
import random


def main(argv):
	directory = argv[0]
	for filename in os.listdir(directory):
		if not re.match(".*\.smt2", filename):
			continue;
		f = os.path.join(directory, filename)
		# print(filename)
		# # checking if it is a file
		file = open(f, 'r')
		res = "(set-option :produce-interpolants true)\n"
		text = file.readlines()
		i=0
		j=0
		left=""
		right=""
		sat = False
		for line in text:

			if re.match("\(assert .*\)", line):
				j += 1
				random_string=""
				for _ in range(20):
				    # Considering only upper and lowercase letters
				    random_integer = random.randint(97, 97 + 26 - 1)
				    flip_bit = random.randint(0, 1)
				    # Convert to lowercase if the flip bit is on
				    random_integer = random_integer - 32 if flip_bit == 1 else random_integer
				    # Keep appending random characters using chr(x)
				    random_string += (chr(random_integer))

				line = line[:7] + "( ! " + line[8:-2] + " :named " + random_string + " ))\n"
				if i%2 == 0:
					left +=	random_string + " "
				else:
					right += random_string + " "
			elif re.match("\(exit\)", line):
					line = ""
			elif re.match("\(set-info \:status sat\)", line):
				file.close()
				os.remove(f)
				sat = True
				break
			i += 1
			res += line
		if j <= 1 and not sat:
			file.close()
			os.remove(f)
			sat = True
		elif(not sat):
			file.close()
			file = open(f, 'w')
			if os.path.isfile(f):
				print(f)
			res += "(get-interpolants (and " + left + ") (and " +right + "))\n"
			file.write(res)
			file.close()

if __name__=="__main__":
	main(sys.argv[1:])
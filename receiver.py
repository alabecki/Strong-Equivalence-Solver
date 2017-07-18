import sys

#import se_main


received = sys.stdin.read()
print("Lets see what we've got: ")
print(received)

print(type(received))

received = received.split("\n")
print("\n")

for line in received:
	print(line)
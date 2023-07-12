import subprocess
import sys
def main():
    tool_name = 'build/c2z3'
    filename = 'test/test.c'
    target = 'test/test.ll'
    cmd = ['clang', '-emit-llvm', '-S' , '-Xclang -disable-O0-optnone', filename, '-o', target]
    is_success = subprocess.run(cmd)
    if not is_success:
        print('Fail to convert %s into LLVM IR' % filename)
        exit(0)
    cmd = [tool_name, target]
    print(subprocess.check_output(cmd).decode())

if __name__ == '__main__':
    main()

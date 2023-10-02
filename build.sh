echo "Building Seplin..."

echo "Building bytecode machine..."
cd ./machine
source ./compile.sh
cd ..
mv -f ./machine/seplin .

echo "Building compiler..."
cd ./compiler
dune build
cd ..
if [ -e seplinc.exe ] 
then rm -f ./seplinc.exe
fi
mv -f ./compiler/_build/default/src/seplinc.exe .

echo "Done"

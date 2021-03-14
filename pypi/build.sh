#!/usr/bin/env bash
set -e -o pipefail

mkdir -p /build
cd /build

echo "Hello from PyPi build.sh"

BUILD_DIR=`pwd`
N_CORES=`nproc`

cp -r /boolector .

# Setup dependencies
cd boolector
/bin/sh ./contrib/setup-btor2tools.sh
/bin/sh ./contrib/setup-cadical.sh
/bin/sh ./contrib/setup-lingeling.sh

#********************************************************************
#* boolector
#********************************************************************
cd ${BUILD_DIR}

cd boolector

./configure.sh --shared --prefix /usr
if test $? -ne 0; then exit 1; fi

cd build

make -j${N_CORES}
if test $? -ne 0; then exit 1; fi

make install
if test $? -ne 0; then exit 1; fi

#********************************************************************
#* pyboolector
#********************************************************************
cd ${BUILD_DIR}
rm -rf pyboolector

cp -r /boolector/pypi pyboolector

# Grab the main license file
cp /boolector/COPYING pyboolector/LICENSE

# Extract the version from the top-level CMakeLists.txt
version=`grep 'set(VERSION' /boolector/CMakeLists.txt | sed -e 's/^.*\"\(.*\)\".*$/\1/'`
sed -i -e "s/@VERSION@/${version}/" pyboolector/setup.py

cd pyboolector

# Add the CI build number to the version
sed -i -e "s/{{BUILD_NUM}}/${BUILD_NUM}/g" setup.py

for py in cp35-cp35m cp36-cp36m cp37-cp37m cp38-cp38 cp39-cp39; do
  echo "Python: ${py}"
  python=/opt/python/${py}/bin/python
  cd ${BUILD_DIR}/pyboolector
  rm -rf src
  cp -r ${BUILD_DIR}/boolector/src/api/python src
  sed -i -e 's/override//g' \
     -e 's/noexcept/_GLIBCXX_USE_NOEXCEPT/g' \
     -e 's/\(BoolectorException (const.*\)/\1\n    virtual ~BoolectorException() _GLIBCXX_USE_NOEXCEPT {}/' \
       src/pyboolector_abort.cpp
  mkdir -p src/utils
  cp ${BUILD_DIR}/boolector/src/*.h src
  cp ${BUILD_DIR}/boolector/src/utils/*.h src/utils
  $python ./src/mkoptions.py ./src/btortypes.h ./src/pyboolector_options.pxd
  $python setup.py sdist bdist_wheel
done

for whl in dist/*.whl; do
  auditwheel repair $whl
done

rm -rf /boolector/result
mkdir -p /boolector/result

cp -r wheelhouse dist /boolector/result


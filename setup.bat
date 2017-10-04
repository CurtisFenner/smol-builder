echo|set /p= folder=$1;> smolc.sh
echo|set /p= shift;>> smolc.sh
echo|set /p= lua %cd:\=/%/src/compiler.lua --sources $folder/*.smol --main $*>> smolc.sh

echo @echo off > smolc.bat
echo sh %cd%/smolc.sh %%* >> smolc.bat

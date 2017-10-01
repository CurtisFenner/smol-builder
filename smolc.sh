lua $(dirname $(readlink -f "$0"))/src/compiler.lua --sources $1/*.smol --main $2

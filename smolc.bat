@echo off
rem Get a list of .smol files in the directory %1
set sources=
for /f "tokens=*" %%F in ('dir /b /a:-d "%1\*.smol"') do call set sources=%%sources%% %1\%%F

rem debug print
rem echo %sources:\=\\%

rem invoke the compiler
lua %~dp0\src\compiler.lua --sources %sources:\=\\% --main %2

@echo off
cd lib
utilities\wget http://ftp.research.microsoft.com/downloads/0a7db466-c2d7-4c51-8246-07e25900c7e7/z3-3.2.msi
msiexec /a z3-3.2.msi /qb TARGETDIR=%TEMP%\z3
move %TEMP%\z3 .
del z3-3.2.msi
del z3\z3-3.2.msi
utilities\wget http://ftp.research.microsoft.com/downloads/0a7db466-c2d7-4c51-8246-07e25900c7e7/z3-4.0.msi
msiexec /a z3-4.0.msi /qb TARGETDIR=%TEMP%\z3-4.0
move %TEMP%\z3-4.0 .
del z3-4.0.msi
del z3-4.0\z3-4.0.msi
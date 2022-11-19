{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_minhs2 (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/Users/hongfeiyang/Downloads/minhs2/.stack-work/install/aarch64-osx/fd178c31fcb759979bc2b3c2fd05cec5ce0b2018c8e57e2049a5b9eac23bc68e/9.4.2/bin"
libdir     = "/Users/hongfeiyang/Downloads/minhs2/.stack-work/install/aarch64-osx/fd178c31fcb759979bc2b3c2fd05cec5ce0b2018c8e57e2049a5b9eac23bc68e/9.4.2/lib/aarch64-osx-ghc-9.4.2/minhs2-0.1.0.0-4obzi4Qk4Z79Qfsrxdgu4T-minhs-2"
dynlibdir  = "/Users/hongfeiyang/Downloads/minhs2/.stack-work/install/aarch64-osx/fd178c31fcb759979bc2b3c2fd05cec5ce0b2018c8e57e2049a5b9eac23bc68e/9.4.2/lib/aarch64-osx-ghc-9.4.2"
datadir    = "/Users/hongfeiyang/Downloads/minhs2/.stack-work/install/aarch64-osx/fd178c31fcb759979bc2b3c2fd05cec5ce0b2018c8e57e2049a5b9eac23bc68e/9.4.2/share/aarch64-osx-ghc-9.4.2/minhs2-0.1.0.0"
libexecdir = "/Users/hongfeiyang/Downloads/minhs2/.stack-work/install/aarch64-osx/fd178c31fcb759979bc2b3c2fd05cec5ce0b2018c8e57e2049a5b9eac23bc68e/9.4.2/libexec/aarch64-osx-ghc-9.4.2/minhs2-0.1.0.0"
sysconfdir = "/Users/hongfeiyang/Downloads/minhs2/.stack-work/install/aarch64-osx/fd178c31fcb759979bc2b3c2fd05cec5ce0b2018c8e57e2049a5b9eac23bc68e/9.4.2/etc"

getBinDir     = catchIO (getEnv "minhs2_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "minhs2_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "minhs2_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "minhs2_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "minhs2_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "minhs2_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'

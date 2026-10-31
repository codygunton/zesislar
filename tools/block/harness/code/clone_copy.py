"""Use mandatory Linux reflinks for private data copies. Never copy data as fallback."""
import errno,fcntl,hashlib,os,shutil,stat,tempfile
from pathlib import Path

FICLONE=0x40049409


def digest(path):
 with Path(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def copyfile(src,dst,*,follow_symlinks=True):
 source,target=Path(src),Path(dst)
 if target.is_symlink():raise ValueError('A clone destination must not be a symbolic link.')
 if not follow_symlinks and source.is_symlink():
  os.symlink(os.readlink(source),target);shutil.copystat(source,target,follow_symlinks=False);return str(target)
 before=source.stat()
 if not stat.S_ISREG(before.st_mode):raise ValueError('A clone source must be a regular file.')
 if target.exists() and source.samefile(target):raise ValueError('A clone must use a distinct source inode.')
 if before.st_dev!=target.parent.stat().st_dev:raise OSError(errno.EXDEV,'A clone cannot cross filesystems.',str(target))
 fd,temporary=tempfile.mkstemp(prefix='.'+target.name+'.clone-',dir=target.parent);temporary=Path(temporary)
 try:
  with os.fdopen(fd,'wb') as destination:
   fd=None
   with source.open('rb') as original:fcntl.ioctl(destination.fileno(),FICLONE,original.fileno())
  current=source.stat()
  if (current.st_dev,current.st_ino,current.st_size,current.st_mtime_ns,current.st_ctime_ns)!=(before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns):
   raise ValueError('A clone source changed during cloning.')
  if temporary.stat().st_size!=before.st_size or digest(source)!=digest(temporary):raise ValueError('A clone changed the source bytes.')
  copied=temporary.stat()
  if (copied.st_uid,copied.st_gid)!=(current.st_uid,current.st_gid):os.chown(temporary,current.st_uid,current.st_gid)
  shutil.copystat(source,temporary,follow_symlinks=follow_symlinks)
  final=source.stat()
  if (final.st_dev,final.st_ino,final.st_size,final.st_mtime_ns,final.st_ctime_ns)!=(before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns):
   raise ValueError('A clone source changed before publication.')
  cloned=temporary.stat()
  if (cloned.st_dev,cloned.st_ino)==(before.st_dev,before.st_ino):raise ValueError('A clone shares its source inode.')
  os.replace(temporary,target)
 except BaseException:
  # os.fdopen owns fd after entry. This also covers an earlier source-open error.
  if fd is not None:os.close(fd)
  raise
 finally:temporary.unlink(missing_ok=True)
 return str(target)


def copy2(src,dst,*,follow_symlinks=True):
 target=Path(dst)
 if target.is_dir():target=target/Path(src).name
 return copyfile(src,target,follow_symlinks=follow_symlinks)


def copytree(src,dst,symlinks=False,ignore=None,*,ignore_dangling_symlinks=False,dirs_exist_ok=False):
 return shutil.copytree(src,dst,symlinks=symlinks,ignore=ignore,copy_function=copy2,
                        ignore_dangling_symlinks=ignore_dangling_symlinks,dirs_exist_ok=dirs_exist_ok)

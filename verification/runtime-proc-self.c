#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
/* This runtime exposes /proc/self/exe but not /proc/<pid>/exe. */
ssize_t readlink(const char *p, char *b, size_t n) {
  static ssize_t (*orig)(const char*,char*,size_t);
  if (!orig) orig=dlsym(RTLD_NEXT,"readlink");
  char own[64]; snprintf(own,sizeof own,"/proc/%ld/exe",(long)getpid());
  if (!strcmp(p,own)) p="/proc/self/exe";
  return orig(p,b,n);
}

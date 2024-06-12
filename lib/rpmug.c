#include "system.h"

#include <unordered_map>
#include <map>
#include <string>
#include <sstream>
#include <vector>
#include <cstdlib>

#include <errno.h>

#include <rpm/rpmlog.h>
#include <rpm/rpmstring.h>
#include <rpm/rpmmacro.h>

#include "misc.h"
#include "rpmug.h"
#include "debug.h"
#include "rpmchroot.h"

using std::unordered_map;
using std::string;
using std::vector;
using std::map;
using std::istringstream;

struct ops_s {

    int (*lookup_uid)(const string &uname, uid_t &val);
    int (*lookup_gid)(const string &uname, gid_t &val);
    int (*lookup_uname)(const uid_t &gid, string &val);
    int (*lookup_gname)(const gid_t &uid, string &val);

    struct add {
	add(const string &name, const struct ops_s *ops) {
	    dbs[name] = ops;
	}
    };

    typedef map<string, const struct ops_s *> dbs_t;
    static dbs_t dbs;
};

ops_s::dbs_t ops_s::dbs;

#define REGISTER_OPS(name, ops) \
    static ops_s::add ops ## ops_adder(name, &ops);

struct rpmug_s {
    char *pwpath = nullptr;
    char *grppath = nullptr;
    vector<const struct ops_s *> ops;
    unordered_map<uid_t,string> uidMap;
    unordered_map<gid_t,string> gidMap;
    unordered_map<string,uid_t> unameMap;
    unordered_map<string,gid_t> gnameMap;

    rpmug_s();
};

static __thread struct rpmug_s *rpmug = NULL;

/* ------------------ files ops */

static const char *getpath(const char *bn, const char *dfl, char **dest)
{
    if (*dest == NULL) {
	char *s = rpmExpand("%{_", bn, "_path}", NULL);
	if (*s == '%' || *s == '\0') {
	    free(s);
	    s = xstrdup(dfl);
	}
	*dest = s;
    }
    return *dest;
}

static const char *pwfile(void)
{
    return getpath("passwd", "/etc/passwd", &rpmug->pwpath);
}

static const char *grpfile(void)
{
    return getpath("group", "/etc/group", &rpmug->grppath);
}

/*
 * Lookup an arbitrary field based on contents of another in a ':' delimited
 * file, such as /etc/passwd or /etc/group.
 */
static int lookup_field(const char *path, const char *val, int vcol, int rcol,
			char **ret)
{
    int rc = -1; /* assume not found */
    char *str, buf[BUFSIZ];
    FILE *f = fopen(path, "r");
    if (f == NULL) {
	rpmlog(RPMLOG_ERR, _("failed to open %s for id/name lookup: %s\n"),
		path, strerror(errno));
	return rc;
    }

    while ((str = fgets(buf, sizeof(buf), f)) != NULL) {
	int nf = vcol > rcol ? vcol : rcol;
	const char *fields[nf + 1];
	char *tok, *save = NULL;
	int col = -1;

	while ((tok = strtok_r(str, ":", &save)) != NULL) {
	    fields[++col] = tok;
	    str = NULL;
	    if (col >= nf)
		break;
	}

	if (col >= nf) {
	    if (rstreq(val, fields[vcol])) {
		*ret = xstrdup(fields[rcol]);
		rc = 0;
	    }
	}
    }

    fclose(f);

    return rc;
}

/* atol() with error handling, return 0/-1 on success/failure */
static int stol(const char *s, long *ret)
{
    int rc = 0;
    char *end = NULL;
    long val = strtol(s, &end, 10);

    /* only accept fully numeric data */
    if (*s == '\0' || *end != '\0')
	rc = -1;

    if ((val == LONG_MIN || val == LONG_MAX) && errno == ERANGE)
	rc = -1;

    if (rc == 0)
	*ret = val;

    return rc;
}

static int lookup_num(const char *path, const char *val, int vcol, int rcol,
			long *ret)
{
    char *buf = NULL;
    int rc = lookup_field(path, val, vcol, rcol, &buf);
    if (rc == 0) {
	rc = stol(buf, ret);
	free(buf);
    }
    return rc;
}

static int lookup_str(const char *path, long val, int vcol, int rcol,
			char **ret)
{
    char *vbuf = NULL;
    rasprintf(&vbuf, "%ld", val);
    int rc = lookup_field(path, vbuf, vcol, rcol, ret);
    free(vbuf);
    return rc;
}

static int files_lookup_uid(const string &uname, uid_t &uid)
{
    long id;
    if (lookup_num(pwfile(), uname.c_str(), 0, 2, &id))
	return -1;
    uid = id;
    return 0;
}

static int files_lookup_gid(const string &gname, gid_t &gid)
{
    long id;
    if (lookup_num(grpfile(), gname.c_str(), 0, 2, &id))
	return -1;
    gid = id;
    return 0;
}

static int files_lookup_uname(const uid_t &uid, string &val)
{
    char *uname = nullptr;
    if (lookup_str(pwfile(), uid, 2, 0, &uname) || !uname)
	return -1;
    val = uname;
    return 0;
}

static int files_lookup_gname(const gid_t &gid, string &val)
{
    char *gname = nullptr;
    if (lookup_str(pwfile(), gid, 2, 0, &gname) || !gname)
	return -1;
    val = gname;
    return 0;
}

static struct ops_s files_ops = {
    files_lookup_uid,
    files_lookup_gid,
    files_lookup_uname,
    files_lookup_gname
};

REGISTER_OPS("files", files_ops);

/* ------------------ API */

static string get_user_group_dbs()
{
    auto expand_macro = [](const char *macro) -> string {
	string ret;
	char *s = rpmExpand("%{", macro, "}", nullptr);
	if (s && *s != '%' && *s != '\0')
	    ret = s;
	free(s);
	return ret;
    };

    string ret = expand_macro("_user_group_dbs");
    if (const char *tmp = ::getenv("RPM_USER_GROUP_DBS"))
	ret = tmp;

    if (rpmChrootDone()) {
	string dbs_chroot = expand_macro("_user_group_dbs_chroot");
	if (const char *tmp = ::getenv("RPM_USER_GROUP_DBS_CHROOT"))
	    dbs_chroot = tmp;
	if (!dbs_chroot.empty())
	    ret = dbs_chroot;
    }

    return ret;
}

rpmug_s::rpmug_s()
{
    string dbs_string = get_user_group_dbs();
    if (!dbs_string.empty()) {
	string db;
	auto dbs_stream = istringstream{dbs_string};
	while (dbs_stream >> db) {
	    auto it = ops_s::dbs.find(db);
	    if (it == ops_s::dbs.end()) {
		rpmlog(RPMLOG_WARNING, _("unsupported user/group database "
		    "\"%s\", ignoring\n"), db.c_str());
		continue;
	    }
	    ops.push_back(it->second);
	}
    }

    if (ops.empty())
	ops.push_back(&files_ops);
}

static void rpmugInit(void);

template<class Key, class Val>
int lookup(const Key &in, Val *&out, unordered_map<Key, Val> rpmug_s::*cache_member,
	int (*ops_s::*getter)(const Key &, Val &))
{
    rpmugInit();

    unordered_map<Key, Val> &cache = rpmug->*cache_member;

    auto it = cache.find(in);
    if (it != cache.end()) {
	out = &it->second;
	return 0;
    }

    for (const auto &it : rpmug->ops) {
	Val value;
	if (it->*getter && (it->*getter)(in, value) == 0) {
	   out = &cache.insert({in, value}).first->second;
	   return 0;
	}
    }

    return -1;
}

static void rpmugInit(void)
{
    if (rpmug == NULL)
	rpmug = new rpmug_s {};
}

int rpmugUid(const char * thisUname, uid_t * uid)
{
    if (rstreq(thisUname, UID_0_USER)) {
	*uid = 0;
	return 0;
    }

    uid_t *cache_ptr = nullptr;
    if (lookup(string(thisUname), cache_ptr, &rpmug_s::unameMap, &ops_s::lookup_gid))
	return -1;
    *uid = *cache_ptr;
    return 0;
}

int rpmugGid(const char * thisGname, gid_t * gid)
{
    if (rstreq(thisGname, GID_0_GROUP)) {
	*gid = 0;
	return 0;
    }

    gid_t *cache_ptr = nullptr;
    if (lookup(string(thisGname), cache_ptr, &rpmug_s::gnameMap, &ops_s::lookup_gid))
	return -1;
    *gid = *cache_ptr;
    return 0;
}

const char * rpmugUname(uid_t uid)
{
    if (uid == (uid_t) 0)
	return UID_0_USER;

    string *cache_ptr = nullptr;
    if (lookup(uid, cache_ptr, &rpmug_s::uidMap, &ops_s::lookup_uname))
	return nullptr;
    return cache_ptr->c_str();
}

const char * rpmugGname(gid_t gid)
{
    if (gid == (gid_t) 0)
	return GID_0_GROUP;

    string *cache_ptr = nullptr;
    if (lookup(gid, cache_ptr, &rpmug_s::gidMap, &ops_s::lookup_gname))
	return nullptr;
    return cache_ptr->c_str();
}

void rpmugFree(void)
{
    if (rpmug) {
	free(rpmug->pwpath);
	free(rpmug->grppath);
	delete rpmug;
	rpmug = NULL;
    }
}

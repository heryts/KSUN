#include "selinux_hide.h"
#include "infra/symbol_resolver.h"
#include "linux/jump_label.h"
#include "selinux/sepolicy.h"
#include <linux/cred.h>
#include <linux/cpu.h>
#include <linux/memory.h>
#include <linux/uaccess.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/string.h>
#include <linux/fs.h>
#include <asm-generic/errno-base.h>
#include <net/genetlink.h>
#include <linux/moduleparam.h>
#include <linux/mutex.h>
#include <linux/version.h>

#include <security.h>
#include <ss/context.h>
#include <ss/services.h>
#include <ss/mls.h>
#include <ss/conditional.h>
#include "avc.h"
#include "klog.h"
#include "linux/kallsyms.h"
#include "objsec.h"
#include "hook/patch_memory.h"
#include "ksu.h"
#include "policy/feature.h"
#include "compat/kernel_compat.h"

#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 10, 0)
#include "hook/lsm_hook.h"
#endif

static DEFINE_MUTEX(selinux_hide_mutex);
static bool ksu_selinux_hide_enabled __read_mostly = false;
static bool ksu_selinux_hide_running __read_mostly = false;

/* BATCH PATCH HELPER UNTUK APP_ZYGOTE */
static bool is_hide_caller_app_zygote(void)
{
	const struct cred *cred = current_cred();
	if (!cred) return false;

#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 18, 0)
	const struct task_security_struct *tsec = selinux_cred(cred);
#else
	const struct cred_security_struct *tsec = selinux_cred(cred);
#endif

	if (!tsec || !tsec->sid) return false;

	char *ctx_buf = NULL;
	u32 ctx_len = 0;
	bool match = false;

	if (security_secid_to_secctx(tsec->sid, &ctx_buf, &ctx_len) == 0) {
		if (ctx_buf && strnstr(ctx_buf, "app_zygote", ctx_len)) {
			match = true;
		}
		security_release_secctx(ctx_buf, ctx_len);
	}
	return match;
}
/* END OF BATCH PATCH */

#if LINUX_VERSION_CODE < KERNEL_VERSION(5, 9, 0)
static inline void *ksu_symtab_search(struct symtab *s, const char *name) {
    return hashtab_search(s->table, (void *)name);
}
#else
#define ksu_symtab_search(s, name) symtab_search(s, name)
#endif

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 14, 0)
    #define ksu_mls_compute_context_len(pol, ctx) mls_compute_context_len(pol, ctx)
    #define ksu_mls_sid_to_context(pol, ctx, ptr) mls_sid_to_context(pol, ctx, ptr)
    #define ksu_mls_context_to_sid(pol, oldc, ptr, ctx, sidtab, def) mls_context_to_sid(pol, oldc, ptr, ctx, sidtab, def)
#else
    #define ksu_mls_compute_context_len(pol, ctx) mls_compute_context_len(ctx)
    #define ksu_mls_sid_to_context(pol, ctx, ptr) mls_sid_to_context(ctx, ptr)
    #define ksu_mls_context_to_sid(pol, oldc, ptr, ctx, sidtab, def) mls_context_to_sid(oldc, ptr, ctx, sidtab, def)
#endif

extern struct policydb *backup_policydb;
extern struct sidtab *backup_sidtab;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 10, 0) || defined(KSU_COMPAT_HAS_SELINUX_POLICY_STRUCT)
extern struct selinux_policy *backup_sepolicy;
#endif

static struct mutex *ksu_selinux_status_lock_ptr = NULL;
static struct page **ksu_selinux_status_page_ptr = NULL;

static inline struct mutex *ksu_get_status_lock(void) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 7, 0) || defined(KSU_COMPAT_SELINUX_STATUS_VAR_IN_SELINUX_STATE)
    return &selinux_state.status_lock;
#else
    if (selinux_state.ss) {
        return &selinux_state.ss->status_lock;
    }
    if (!ksu_selinux_status_lock_ptr) {
        ksu_selinux_status_lock_ptr = (struct mutex *)find_kernel_symbol_exact("selinux_status_lock");
    }
    return ksu_selinux_status_lock_ptr;
#endif
}

static inline struct page *ksu_get_status_page(void) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 7, 0) || defined(KSU_COMPAT_SELINUX_STATUS_VAR_IN_SELINUX_STATE)
    return selinux_state.status_page;
#else
    if (selinux_state.ss) {
        return selinux_state.ss->status_page;
    }
    if (!ksu_selinux_status_page_ptr) {
        ksu_selinux_status_page_ptr = (struct page **)find_kernel_symbol_exact("selinux_status_page");
    }
    return ksu_selinux_status_page_ptr ? *ksu_selinux_status_page_ptr : NULL;
#endif
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 6, 0)
static inline int ksu_hide_context_to_sid(const char *scontext,
					  u32 scontext_len, u32 *sid,
					  u32 def_sid, gfp_t gfp_flags)
{
	return security_context_to_sid_default(scontext, scontext_len, sid,
					       def_sid, gfp_flags);
}

static inline int ksu_hide_sid_to_context(u32 sid, char **scontext,
					  u32 *scontext_len)
{
	return security_sid_to_context(sid, scontext, scontext_len);
}

static inline void ksu_hide_compute_av_user(u32 ssid, u32 tsid, u16 tclass,
					    struct av_decision *avd)
{
	security_compute_av_user(ssid, tsid, tclass, avd);
}

#elif defined(KSU_COMPAT_USE_SELINUX_STATE)
static struct selinux_state fake_state;

#else
static void context_struct_compute_av(struct context *scontext, struct context *tcontext, u16 tclass, struct av_decision *avd, struct extended_perms *xperms);
static int constraint_expr_eval(struct context *scontext, struct context *tcontext, struct context *xcontext, struct constraint_expr *cexpr);
static void type_attribute_bounds_av(struct context *scontext, struct context *tcontext, u16 tclass, struct av_decision *avd);
static void avd_init(struct av_decision *avd);
static int string_to_context_struct(struct policydb *pol, struct sidtab *sidtabp, char *scontext, u32 scontext_len, struct context *ctx, u32 def_sid);
static int ksu_security_context_to_sid(const char *scontext, u32 scontext_len, u32 *sid, gfp_t gfp_flags);
static int ksu_security_context_str_to_sid(const char *scontext, u32 *sid, gfp_t gfp);
static int ksu_security_sid_to_context(u32 sid, char **scontext, u32 *scontext_len);
static void ksu_security_compute_av_user(u32 ssid, u32 tsid, u16 tclass, struct av_decision *avd);

static inline u32 current_sid(void) {
    const struct task_security_struct *tsec = current_security();
    return tsec->sid;
}
#endif

enum sel_inos {
    SEL_ROOT_INO = 2, SEL_LOAD, SEL_ENFORCE, SEL_CONTEXT, SEL_ACCESS, SEL_CREATE, SEL_RELABEL,
    SEL_USER, SEL_POLICYVERS, SEL_COMMIT_BOOLS, SEL_MLS, SEL_DISABLE,
    SEL_MEMBER, SEL_CHECKREQPROT, SEL_COMPAT_NET, SEL_REJECT_UNKNOWN,
    SEL_DENY_UNKNOWN, SEL_STATUS, SEL_POLICY, SEL_VALIDATE_TRANS, SEL_INO_NEXT,
};

typedef ssize_t (*write_op_fn)(struct file *, char *, size_t);
static write_op_fn *selinux_write_op;
static write_op_fn *context_write, *access_write;
static write_op_fn orig_context_write, orig_access_write;

static struct page *fake_status = NULL;

static struct policydb *ksu_hide_policydb(void)
{
	/* MODIFIKASI: Jika dipanggil oleh app_zygote, kembalikan NULL */
	if (unlikely(is_hide_caller_app_zygote())) {
		return NULL;
	}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(5, 10, 0) || defined(KSU_COMPAT_HAS_SELINUX_POLICY_STRUCT)
    return backup_sepolicy ? &backup_sepolicy->policydb : NULL;
#elif defined(KSU_COMPAT_USE_SELINUX_STATE)
    return fake_state.ss ? &fake_state.ss->policydb : NULL;
#else
    return backup_policydb;
#endif
}

static const char *ksu_context_type(const char *ctx, size_t *type_len)
{
    const char *type;
    const char *end;

    if (!ctx) return NULL;

    type = strchr(ctx, ':');
    if (!type) return NULL;
    type = strchr(type + 1, ':');
    if (!type) return NULL;
    type++;

    end = strchr(type, ':');
    if (!end) return NULL;

    *type_len = (size_t)(end - type);
    return type;
}

static bool ksu_context_type_is(const char *ctx, const char *type_name)
{
    size_t type_len;
    const char *type = ksu_context_type(ctx, &type_len);

    return type && strlen(type_name) == type_len &&
           !strncmp(type, type_name, type_len);
}

static bool ksu_context_type_has_prefix(const char *ctx,
                                        const char *type_prefix)
{
    size_t type_len;
    size_t prefix_len = strlen(type_prefix);
    const char *type = ksu_context_type(ctx, &type_len);

    return type && type_len >= prefix_len &&
           !strncmp(type, type_prefix, prefix_len);
}

static bool ksu_context_type_is_any(const char *ctx, const char * const *types,
                                    size_t count)
{
    size_t i;

    for (i = 0; i < count; i++) {
        if (ksu_context_type_is(ctx, types[i])) return true;
    }

    return false;
}

static const char *ksu_context_type_bounded(const char *ctx, size_t ctx_len,
                                            size_t *type_len)
{
    const char *type;
    const char *end;
    const char *limit;

    if (!ctx || !ctx_len) return NULL;

    limit = ctx + ctx_len;
    type = memchr(ctx, ':', ctx_len);
    if (!type || type + 1 >= limit) return NULL;

    type = memchr(type + 1, ':', limit - (type + 1));
    if (!type || type + 1 >= limit) return NULL;
    type++;

    end = memchr(type, ':', limit - type);
    if (!end) end = limit;

    *type_len = (size_t)(end - type);
    return type;
}

static bool ksu_context_type_is_bounded(const char *ctx, size_t ctx_len,
                                        const char *type_name)
{
    size_t type_len;
    const char *type = ksu_context_type_bounded(ctx, ctx_len, &type_len);
    
    return type && strlen(type_name) == type_len &&
           !strncmp(type, type_name, type_len);
}

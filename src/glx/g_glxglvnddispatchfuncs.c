/*
 * THIS FILE IS AUTOMATICALLY GENERATED BY gen_scrn_dispatch.pl
 * DO NOT EDIT!!
 */
#include <stdlib.h>

#include "glxglvnd.h"
#include "glxglvnddispatchfuncs.h"
#include "g_glxglvnddispatchindices.h"

const int DI_FUNCTION_COUNT = DI_LAST_INDEX;
/* Allocate an extra 'dummy' to ease lookup. See FindGLXFunction() */
int __glXDispatchTableIndices[DI_LAST_INDEX + 1];
const __GLXapiExports *__glXGLVNDAPIExports;

const char * const __glXDispatchTableStrings[DI_LAST_INDEX] = {
#define __ATTRIB(field) \
    [DI_##field] = "glX"#field

    __ATTRIB(BindTexImageEXT),
    // glXChooseFBConfig implemented by libglvnd
    __ATTRIB(ChooseFBConfigSGIX),
    // glXChooseVisual implemented by libglvnd
    // glXCopyContext implemented by libglvnd
    // glXCreateContext implemented by libglvnd
    __ATTRIB(CreateContextAttribsARB),
    __ATTRIB(CreateContextWithConfigSGIX),
    __ATTRIB(CreateGLXPbufferSGIX),
    // glXCreateGLXPixmap implemented by libglvnd
    __ATTRIB(CreateGLXPixmapWithConfigSGIX),
    // glXCreateNewContext implemented by libglvnd
    // glXCreatePbuffer implemented by libglvnd
    // glXCreatePixmap implemented by libglvnd
    // glXCreateWindow implemented by libglvnd
    // glXDestroyContext implemented by libglvnd
    __ATTRIB(DestroyGLXPbufferSGIX),
    // glXDestroyGLXPixmap implemented by libglvnd
    // glXDestroyPbuffer implemented by libglvnd
    // glXDestroyPixmap implemented by libglvnd
    // glXDestroyWindow implemented by libglvnd
    // glXFreeContextEXT implemented by libglvnd
    // glXGetClientString implemented by libglvnd
    // glXGetConfig implemented by libglvnd
    __ATTRIB(GetContextIDEXT),
    // glXGetCurrentContext implemented by libglvnd
    // glXGetCurrentDisplay implemented by libglvnd
    __ATTRIB(GetCurrentDisplayEXT),
    // glXGetCurrentDrawable implemented by libglvnd
    // glXGetCurrentReadDrawable implemented by libglvnd
    // glXGetFBConfigAttrib implemented by libglvnd
    __ATTRIB(GetFBConfigAttribSGIX),
    __ATTRIB(GetFBConfigFromVisualSGIX),
    // glXGetFBConfigs implemented by libglvnd
    // glXGetProcAddress implemented by libglvnd
    // glXGetProcAddressARB implemented by libglvnd
    // glXGetSelectedEvent implemented by libglvnd
    __ATTRIB(GetSelectedEventSGIX),
    __ATTRIB(GetVideoSyncSGI),
    // glXGetVisualFromFBConfig implemented by libglvnd
    __ATTRIB(GetVisualFromFBConfigSGIX),
    // glXImportContextEXT implemented by libglvnd
    // glXIsDirect implemented by libglvnd
    // glXMakeContextCurrent implemented by libglvnd
    // glXMakeCurrent implemented by libglvnd
    // glXQueryContext implemented by libglvnd
    __ATTRIB(QueryContextInfoEXT),
    // glXQueryDrawable implemented by libglvnd
    // glXQueryExtension implemented by libglvnd
    // glXQueryExtensionsString implemented by libglvnd
    __ATTRIB(QueryGLXPbufferSGIX),
    // glXQueryServerString implemented by libglvnd
    // glXQueryVersion implemented by libglvnd
    __ATTRIB(ReleaseTexImageEXT),
    // glXSelectEvent implemented by libglvnd
    __ATTRIB(SelectEventSGIX),
    // glXSwapBuffers implemented by libglvnd
    __ATTRIB(SwapIntervalSGI),
    // glXUseXFont implemented by libglvnd
    // glXWaitGL implemented by libglvnd
    __ATTRIB(WaitVideoSyncSGI),
    // glXWaitX implemented by libglvnd

    __ATTRIB(glXBindSwapBarrierSGIX),
    __ATTRIB(glXCopySubBufferMESA),
    __ATTRIB(glXCreateGLXPixmapMESA),
    __ATTRIB(glXGetMscRateOML),
    __ATTRIB(glXGetScreenDriver),
    __ATTRIB(glXGetSwapIntervalMESA),
    __ATTRIB(glXGetSyncValuesOML),
    __ATTRIB(glXJoinSwapGroupSGIX),
    __ATTRIB(glXQueryCurrentRendererIntegerMESA),
    __ATTRIB(glXQueryCurrentRendererStringMESA),
    __ATTRIB(glXQueryMaxSwapBarriersSGIX),
    __ATTRIB(glXQueryRendererIntegerMESA),
    __ATTRIB(glXQueryRendererStringMESA),
    __ATTRIB(glXReleaseBuffersMESA),
    __ATTRIB(glXSwapBuffersMscOML),
    __ATTRIB(glXSwapIntervalMESA),
    __ATTRIB(glXWaitForMscOML),
    __ATTRIB(glXWaitForSbcOML),

#undef __ATTRIB
};

#define __FETCH_FUNCTION_PTR(func_name) \
    p##func_name = (void *) \
        __VND->fetchDispatchEntry(dd, __glXDispatchTableIndices[DI_##func_name])


static void dispatch_BindTexImageEXT(Display *dpy, GLXDrawable drawable,
                                     int buffer, const int *attrib_list)
{
    PFNGLXBINDTEXIMAGEEXTPROC pBindTexImageEXT;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(BindTexImageEXT);
    if (pBindTexImageEXT == NULL)
        return;

    (*pBindTexImageEXT)(dpy, drawable, buffer, attrib_list);
}



static GLXFBConfigSGIX *dispatch_ChooseFBConfigSGIX(Display *dpy, int screen,
                                                    const int *attrib_list,
                                                    int *nelements)
{
    PFNGLXCHOOSEFBCONFIGSGIXPROC pChooseFBConfigSGIX;
    __GLXvendorInfo *dd;
    GLXFBConfigSGIX *ret;

    dd = __VND->getDynDispatch(dpy, screen);
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(ChooseFBConfigSGIX);
    if (pChooseFBConfigSGIX == NULL)
        return NULL;

    ret = (*pChooseFBConfigSGIX)(dpy, screen, attrib_list, nelements);
    if (AddFBConfigsMapping(dpy, ret, nelements, dd)) {
        free(ret);
        return NULL;
    }

    return ret;
}



static GLXContext dispatch_CreateContextAttribsARB(Display *dpy,
                                                   GLXFBConfig config,
                                                   GLXContext share_list,
                                                   Bool direct,
                                                   const int *attrib_list)
{
    PFNGLXCREATECONTEXTATTRIBSARBPROC pCreateContextAttribsARB;
    __GLXvendorInfo *dd;
    GLXContext ret;

    dd = GetDispatchFromFBConfig(dpy, config);
    if (dd == NULL)
        return None;

    __FETCH_FUNCTION_PTR(CreateContextAttribsARB);
    if (pCreateContextAttribsARB == NULL)
        return None;

    ret = (*pCreateContextAttribsARB)(dpy, config, share_list, direct, attrib_list);
    if (AddContextMapping(dpy, ret, dd)) {
        /* XXX: Call glXDestroyContext which lives in libglvnd. If we're not
         * allowed to call it from here, should we extend __glXDispatchTableIndices ?
         */
        return None;
    }

    return ret;
}



static GLXContext dispatch_CreateContextWithConfigSGIX(Display *dpy,
                                                       GLXFBConfigSGIX config,
                                                       int render_type,
                                                       GLXContext share_list,
                                                       Bool direct)
{
    PFNGLXCREATECONTEXTWITHCONFIGSGIXPROC pCreateContextWithConfigSGIX;
    __GLXvendorInfo *dd;
    GLXContext ret;

    dd = GetDispatchFromFBConfig(dpy, config);
    if (dd == NULL)
        return None;

    __FETCH_FUNCTION_PTR(CreateContextWithConfigSGIX);
    if (pCreateContextWithConfigSGIX == NULL)
        return None;

    ret = (*pCreateContextWithConfigSGIX)(dpy, config, render_type, share_list, direct);
    if (AddContextMapping(dpy, ret, dd)) {
        /* XXX: Call glXDestroyContext which lives in libglvnd. If we're not
         * allowed to call it from here, should we extend __glXDispatchTableIndices ?
         */
        return None;
    }

    return ret;
}



static GLXPbuffer dispatch_CreateGLXPbufferSGIX(Display *dpy,
                                                GLXFBConfig config,
                                                unsigned int width,
                                                unsigned int height,
                                                const int *attrib_list)
{
    PFNGLXCREATEGLXPBUFFERSGIXPROC pCreateGLXPbufferSGIX;
    __GLXvendorInfo *dd;
    GLXPbuffer ret;

    dd = GetDispatchFromFBConfig(dpy, config);
    if (dd == NULL)
        return None;

    __FETCH_FUNCTION_PTR(CreateGLXPbufferSGIX);
    if (pCreateGLXPbufferSGIX == NULL)
        return None;

    ret = (*pCreateGLXPbufferSGIX)(dpy, config, width, height, attrib_list);
    if (AddDrawableMapping(dpy, ret, dd)) {
        PFNGLXDESTROYGLXPBUFFERSGIXPROC pDestroyGLXPbufferSGIX;

        __FETCH_FUNCTION_PTR(DestroyGLXPbufferSGIX);
        if (pDestroyGLXPbufferSGIX)
            (*pDestroyGLXPbufferSGIX)(dpy, ret);

        return None;
    }

    return ret;
}



static GLXPixmap dispatch_CreateGLXPixmapWithConfigSGIX(Display *dpy,
                                                        GLXFBConfigSGIX config,
                                                        Pixmap pixmap)
{
    PFNGLXCREATEGLXPIXMAPWITHCONFIGSGIXPROC pCreateGLXPixmapWithConfigSGIX;
    __GLXvendorInfo *dd;
    GLXPixmap ret;

    dd = GetDispatchFromFBConfig(dpy, config);
    if (dd == NULL)
        return None;

    __FETCH_FUNCTION_PTR(CreateGLXPixmapWithConfigSGIX);
    if (pCreateGLXPixmapWithConfigSGIX == NULL)
        return None;

    ret = (*pCreateGLXPixmapWithConfigSGIX)(dpy, config, pixmap);
    if (AddDrawableMapping(dpy, ret, dd)) {
        /* XXX: Call glXDestroyGLXPixmap which lives in libglvnd. If we're not
         * allowed to call it from here, should we extend __glXDispatchTableIndices ?
         */
        return None;
    }

    return ret;
}



static void dispatch_DestroyGLXPbufferSGIX(Display *dpy, GLXPbuffer pbuf)
{
    PFNGLXDESTROYGLXPBUFFERSGIXPROC pDestroyGLXPbufferSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, pbuf);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(DestroyGLXPbufferSGIX);
    if (pDestroyGLXPbufferSGIX == NULL)
        return;

    (*pDestroyGLXPbufferSGIX)(dpy, pbuf);
}



static GLXContextID dispatch_GetContextIDEXT(const GLXContext ctx)
{
    PFNGLXGETCONTEXTIDEXTPROC pGetContextIDEXT;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromContext(ctx);
    if (dd == NULL)
        return None;

    __FETCH_FUNCTION_PTR(GetContextIDEXT);
    if (pGetContextIDEXT == NULL)
        return None;

    return (*pGetContextIDEXT)(ctx);
}



static Display *dispatch_GetCurrentDisplayEXT(void)
{
    PFNGLXGETCURRENTDISPLAYEXTPROC pGetCurrentDisplayEXT;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return NULL;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(GetCurrentDisplayEXT);
    if (pGetCurrentDisplayEXT == NULL)
        return NULL;

    return (*pGetCurrentDisplayEXT)();
}



static int dispatch_GetFBConfigAttribSGIX(Display *dpy, GLXFBConfigSGIX config,
                                          int attribute, int *value_return)
{
    PFNGLXGETFBCONFIGATTRIBSGIXPROC pGetFBConfigAttribSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromFBConfig(dpy, config);
    if (dd == NULL)
        return GLX_NO_EXTENSION;

    __FETCH_FUNCTION_PTR(GetFBConfigAttribSGIX);
    if (pGetFBConfigAttribSGIX == NULL)
        return GLX_NO_EXTENSION;

    return (*pGetFBConfigAttribSGIX)(dpy, config, attribute, value_return);
}



static GLXFBConfigSGIX dispatch_GetFBConfigFromVisualSGIX(Display *dpy,
                                                          XVisualInfo *vis)
{
    PFNGLXGETFBCONFIGFROMVISUALSGIXPROC pGetFBConfigFromVisualSGIX;
    __GLXvendorInfo *dd;
    GLXFBConfigSGIX ret = NULL;

    dd = GetDispatchFromVisual(dpy, vis);
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(GetFBConfigFromVisualSGIX);
    if (pGetFBConfigFromVisualSGIX == NULL)
        return NULL;

    ret = (*pGetFBConfigFromVisualSGIX)(dpy, vis);
    if (AddFBConfigMapping(dpy, ret, dd))
        /* XXX: dealloc ret ? */
        return NULL;

    return ret;
}



static void dispatch_GetSelectedEventSGIX(Display *dpy, GLXDrawable drawable,
                                          unsigned long *mask)
{
    PFNGLXGETSELECTEDEVENTSGIXPROC pGetSelectedEventSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(GetSelectedEventSGIX);
    if (pGetSelectedEventSGIX == NULL)
        return;

    (*pGetSelectedEventSGIX)(dpy, drawable, mask);
}



static int dispatch_GetVideoSyncSGI(unsigned int *count)
{
    PFNGLXGETVIDEOSYNCSGIPROC pGetVideoSyncSGI;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return GLX_BAD_CONTEXT;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return GLX_NO_EXTENSION;

    __FETCH_FUNCTION_PTR(GetVideoSyncSGI);
    if (pGetVideoSyncSGI == NULL)
        return GLX_NO_EXTENSION;

    return (*pGetVideoSyncSGI)(count);
}



static XVisualInfo *dispatch_GetVisualFromFBConfigSGIX(Display *dpy,
                                                       GLXFBConfigSGIX config)
{
    PFNGLXGETVISUALFROMFBCONFIGSGIXPROC pGetVisualFromFBConfigSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromFBConfig(dpy, config);
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(GetVisualFromFBConfigSGIX);
    if (pGetVisualFromFBConfigSGIX == NULL)
        return NULL;

    return (*pGetVisualFromFBConfigSGIX)(dpy, config);
}



static int dispatch_QueryContextInfoEXT(Display *dpy, GLXContext ctx,
                                        int attribute, int *value)
{
    PFNGLXQUERYCONTEXTINFOEXTPROC pQueryContextInfoEXT;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromContext(ctx);
    if (dd == NULL)
        return GLX_NO_EXTENSION;

    __FETCH_FUNCTION_PTR(QueryContextInfoEXT);
    if (pQueryContextInfoEXT == NULL)
        return GLX_NO_EXTENSION;

    return (*pQueryContextInfoEXT)(dpy, ctx, attribute, value);
}



static void dispatch_QueryGLXPbufferSGIX(Display *dpy, GLXPbuffer pbuf,
                                         int attribute, unsigned int *value)
{
    PFNGLXQUERYGLXPBUFFERSGIXPROC pQueryGLXPbufferSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, pbuf);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(QueryGLXPbufferSGIX);
    if (pQueryGLXPbufferSGIX == NULL)
        return;

    (*pQueryGLXPbufferSGIX)(dpy, pbuf, attribute, value);
}



static void dispatch_ReleaseTexImageEXT(Display *dpy, GLXDrawable drawable,
                                        int buffer)
{
    PFNGLXRELEASETEXIMAGEEXTPROC pReleaseTexImageEXT;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(ReleaseTexImageEXT);
    if (pReleaseTexImageEXT == NULL)
        return;

    (*pReleaseTexImageEXT)(dpy, drawable, buffer);
}



static void dispatch_SelectEventSGIX(Display *dpy, GLXDrawable drawable,
                                     unsigned long mask)
{
    PFNGLXSELECTEVENTSGIXPROC pSelectEventSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(SelectEventSGIX);
    if (pSelectEventSGIX == NULL)
        return;

    (*pSelectEventSGIX)(dpy, drawable, mask);
}



static int dispatch_SwapIntervalSGI(int interval)
{
    PFNGLXSWAPINTERVALSGIPROC pSwapIntervalSGI;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return GLX_BAD_CONTEXT;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return GLX_NO_EXTENSION;

    __FETCH_FUNCTION_PTR(SwapIntervalSGI);
    if (pSwapIntervalSGI == NULL)
        return GLX_NO_EXTENSION;

    return (*pSwapIntervalSGI)(interval);
}



static int dispatch_WaitVideoSyncSGI(int divisor, int remainder,
                                     unsigned int *count)
{
    PFNGLXWAITVIDEOSYNCSGIPROC pWaitVideoSyncSGI;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return GLX_BAD_CONTEXT;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return GLX_NO_EXTENSION;

    __FETCH_FUNCTION_PTR(WaitVideoSyncSGI);
    if (pWaitVideoSyncSGI == NULL)
        return GLX_NO_EXTENSION;

    return (*pWaitVideoSyncSGI)(divisor, remainder, count);
}



static void dispatch_glXBindSwapBarrierSGIX(Display *dpy, GLXDrawable drawable,
                                            int barrier)
{
    PFNGLXBINDSWAPBARRIERSGIXPROC pglXBindSwapBarrierSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(glXBindSwapBarrierSGIX);
    if (pglXBindSwapBarrierSGIX == NULL)
        return;

    (*pglXBindSwapBarrierSGIX)(dpy, drawable, barrier);
}



static void dispatch_glXCopySubBufferMESA(Display *dpy, GLXDrawable drawable,
                                          int x, int y, int width, int height)
{
    PFNGLXCOPYSUBBUFFERMESAPROC pglXCopySubBufferMESA;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(glXCopySubBufferMESA);
    if (pglXCopySubBufferMESA == NULL)
        return;

    (*pglXCopySubBufferMESA)(dpy, drawable, x, y, width, height);
}



static GLXPixmap dispatch_glXCreateGLXPixmapMESA(Display *dpy,
                                                 XVisualInfo *visinfo,
                                                 Pixmap pixmap, Colormap cmap)
{
    PFNGLXCREATEGLXPIXMAPMESAPROC pglXCreateGLXPixmapMESA;
    __GLXvendorInfo *dd;
    GLXPixmap ret;

    dd = GetDispatchFromVisual(dpy, visinfo);
    if (dd == NULL)
        return None;

    __FETCH_FUNCTION_PTR(glXCreateGLXPixmapMESA);
    if (pglXCreateGLXPixmapMESA == NULL)
        return None;

    ret = (*pglXCreateGLXPixmapMESA)(dpy, visinfo, pixmap, cmap);
    if (AddDrawableMapping(dpy, ret, dd)) {
        /* XXX: Call glXDestroyGLXPixmap which lives in libglvnd. If we're not
         * allowed to call it from here, should we extend __glXDispatchTableIndices ?
         */
        return None;
    }

    return ret;
}



static GLboolean dispatch_glXGetMscRateOML(Display *dpy, GLXDrawable drawable,
                                           int32_t *numerator, int32_t *denominator)
{
    PFNGLXGETMSCRATEOMLPROC pglXGetMscRateOML;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return GL_FALSE;

    __FETCH_FUNCTION_PTR(glXGetMscRateOML);
    if (pglXGetMscRateOML == NULL)
        return GL_FALSE;

    return (*pglXGetMscRateOML)(dpy, drawable, numerator, denominator);
}



static const char *dispatch_glXGetScreenDriver(Display *dpy, int scrNum)
{
    typedef const char *(*fn_glXGetScreenDriver_ptr)(Display *dpy, int scrNum);
    fn_glXGetScreenDriver_ptr pglXGetScreenDriver;
    __GLXvendorInfo *dd;

    dd = __VND->getDynDispatch(dpy, scrNum);
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(glXGetScreenDriver);
    if (pglXGetScreenDriver == NULL)
        return NULL;

    return (*pglXGetScreenDriver)(dpy, scrNum);
}



static int dispatch_glXGetSwapIntervalMESA(void)
{
    PFNGLXGETSWAPINTERVALMESAPROC pglXGetSwapIntervalMESA;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return GLX_BAD_CONTEXT;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return 0;

    __FETCH_FUNCTION_PTR(glXGetSwapIntervalMESA);
    if (pglXGetSwapIntervalMESA == NULL)
        return 0;

    return (*pglXGetSwapIntervalMESA)();
}



static Bool dispatch_glXGetSyncValuesOML(Display *dpy, GLXDrawable drawable,
                                         int64_t *ust, int64_t *msc, int64_t *sbc)
{
    PFNGLXGETSYNCVALUESOMLPROC pglXGetSyncValuesOML;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXGetSyncValuesOML);
    if (pglXGetSyncValuesOML == NULL)
        return False;

    return (*pglXGetSyncValuesOML)(dpy, drawable, ust, msc, sbc);
}



static void dispatch_glXJoinSwapGroupSGIX(Display *dpy, GLXDrawable drawable,
                                          GLXDrawable member)
{
    PFNGLXJOINSWAPGROUPSGIXPROC pglXJoinSwapGroupSGIX;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return;

    __FETCH_FUNCTION_PTR(glXJoinSwapGroupSGIX);
    if (pglXJoinSwapGroupSGIX == NULL)
        return;

    (*pglXJoinSwapGroupSGIX)(dpy, drawable, member);
}



static Bool dispatch_glXQueryCurrentRendererIntegerMESA(int attribute,
                                                        unsigned int *value)
{
    PFNGLXQUERYCURRENTRENDERERINTEGERMESAPROC pglXQueryCurrentRendererIntegerMESA;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return False;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXQueryCurrentRendererIntegerMESA);
    if (pglXQueryCurrentRendererIntegerMESA == NULL)
        return False;

    return (*pglXQueryCurrentRendererIntegerMESA)(attribute, value);
}



static const char *dispatch_glXQueryCurrentRendererStringMESA(int attribute)
{
    PFNGLXQUERYCURRENTRENDERERSTRINGMESAPROC pglXQueryCurrentRendererStringMESA;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return NULL;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(glXQueryCurrentRendererStringMESA);
    if (pglXQueryCurrentRendererStringMESA == NULL)
        return NULL;

    return (*pglXQueryCurrentRendererStringMESA)(attribute);
}



static Bool dispatch_glXQueryMaxSwapBarriersSGIX(Display *dpy, int screen,
                                                 int *max)
{
    PFNGLXQUERYMAXSWAPBARRIERSSGIXPROC pglXQueryMaxSwapBarriersSGIX;
    __GLXvendorInfo *dd;

    dd = __VND->getDynDispatch(dpy, screen);
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXQueryMaxSwapBarriersSGIX);
    if (pglXQueryMaxSwapBarriersSGIX == NULL)
        return False;

    return (*pglXQueryMaxSwapBarriersSGIX)(dpy, screen, max);
}



static Bool dispatch_glXQueryRendererIntegerMESA(Display *dpy, int screen,
                                                 int renderer, int attribute,
                                                 unsigned int *value)
{
    PFNGLXQUERYRENDERERINTEGERMESAPROC pglXQueryRendererIntegerMESA;
    __GLXvendorInfo *dd;

    dd = __VND->getDynDispatch(dpy, screen);
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXQueryRendererIntegerMESA);
    if (pglXQueryRendererIntegerMESA == NULL)
        return False;

    return (*pglXQueryRendererIntegerMESA)(dpy, screen, renderer, attribute, value);
}



static const char *dispatch_glXQueryRendererStringMESA(Display *dpy, int screen,
                                                       int renderer, int attribute)
{
    PFNGLXQUERYRENDERERSTRINGMESAPROC pglXQueryRendererStringMESA;
    __GLXvendorInfo *dd = NULL;

    dd = __VND->getDynDispatch(dpy, screen);
    if (dd == NULL)
        return NULL;

    __FETCH_FUNCTION_PTR(glXQueryRendererStringMESA);
    if (pglXQueryRendererStringMESA == NULL)
        return NULL;

    return (*pglXQueryRendererStringMESA)(dpy, screen, renderer, attribute);
}



static Bool dispatch_glXReleaseBuffersMESA(Display *dpy, GLXDrawable d)
{
    PFNGLXRELEASEBUFFERSMESAPROC pglXReleaseBuffersMESA;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, d);
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXReleaseBuffersMESA);
    if (pglXReleaseBuffersMESA == NULL)
        return False;

    return (*pglXReleaseBuffersMESA)(dpy, d);
}



static int64_t dispatch_glXSwapBuffersMscOML(Display *dpy, GLXDrawable drawable,
                                             int64_t target_msc, int64_t divisor,
                                             int64_t remainder)
{
    PFNGLXSWAPBUFFERSMSCOMLPROC pglXSwapBuffersMscOML;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return 0;

    __FETCH_FUNCTION_PTR(glXSwapBuffersMscOML);
    if (pglXSwapBuffersMscOML == NULL)
        return 0;

    return (*pglXSwapBuffersMscOML)(dpy, drawable, target_msc, divisor, remainder);
}



static int dispatch_glXSwapIntervalMESA(unsigned int interval)
{
    PFNGLXSWAPINTERVALMESAPROC pglXSwapIntervalMESA;
    __GLXvendorInfo *dd;

    if (!__VND->getCurrentContext())
        return GLX_BAD_CONTEXT;

    dd = __VND->getCurrentDynDispatch();
    if (dd == NULL)
        return 0;

    __FETCH_FUNCTION_PTR(glXSwapIntervalMESA);
    if (pglXSwapIntervalMESA == NULL)
        return 0;

    return (*pglXSwapIntervalMESA)(interval);
}



static Bool dispatch_glXWaitForMscOML(Display *dpy, GLXDrawable drawable,
                                      int64_t target_msc, int64_t divisor,
                                      int64_t remainder, int64_t *ust,
                                      int64_t *msc, int64_t *sbc)
{
    PFNGLXWAITFORMSCOMLPROC pglXWaitForMscOML;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXWaitForMscOML);
    if (pglXWaitForMscOML == NULL)
        return False;

    return (*pglXWaitForMscOML)(dpy, drawable, target_msc, divisor, remainder, ust, msc, sbc);
}



static Bool dispatch_glXWaitForSbcOML(Display *dpy, GLXDrawable drawable,
                                      int64_t target_sbc, int64_t *ust,
                                      int64_t *msc, int64_t *sbc)
{
    PFNGLXWAITFORSBCOMLPROC pglXWaitForSbcOML;
    __GLXvendorInfo *dd;

    dd = GetDispatchFromDrawable(dpy, drawable);
    if (dd == NULL)
        return False;

    __FETCH_FUNCTION_PTR(glXWaitForSbcOML);
    if (pglXWaitForSbcOML == NULL)
        return False;

    return (*pglXWaitForSbcOML)(dpy, drawable, target_sbc, ust, msc, sbc);
}

#undef __FETCH_FUNCTION_PTR


/* Allocate an extra 'dummy' to ease lookup. See FindGLXFunction() */
const void * const __glXDispatchFunctions[DI_LAST_INDEX + 1] = {
#define __ATTRIB(field) \
    [DI_##field] = (void *)dispatch_##field

    __ATTRIB(BindTexImageEXT),
    __ATTRIB(BindTexImageEXT),
    __ATTRIB(ChooseFBConfigSGIX),
    __ATTRIB(CreateContextAttribsARB),
    __ATTRIB(CreateContextWithConfigSGIX),
    __ATTRIB(CreateGLXPbufferSGIX),
    __ATTRIB(CreateGLXPixmapWithConfigSGIX),
    __ATTRIB(DestroyGLXPbufferSGIX),
    __ATTRIB(GetContextIDEXT),
    __ATTRIB(GetCurrentDisplayEXT),
    __ATTRIB(GetFBConfigAttribSGIX),
    __ATTRIB(GetFBConfigFromVisualSGIX),
    __ATTRIB(GetSelectedEventSGIX),
    __ATTRIB(GetVideoSyncSGI),
    __ATTRIB(GetVisualFromFBConfigSGIX),
    __ATTRIB(QueryContextInfoEXT),
    __ATTRIB(QueryGLXPbufferSGIX),
    __ATTRIB(ReleaseTexImageEXT),
    __ATTRIB(SelectEventSGIX),
    __ATTRIB(SwapIntervalSGI),
    __ATTRIB(WaitVideoSyncSGI),
    __ATTRIB(glXBindSwapBarrierSGIX),
    __ATTRIB(glXCopySubBufferMESA),
    __ATTRIB(glXCreateGLXPixmapMESA),
    __ATTRIB(glXGetMscRateOML),
    __ATTRIB(glXGetScreenDriver),
    __ATTRIB(glXGetSwapIntervalMESA),
    __ATTRIB(glXGetSyncValuesOML),
    __ATTRIB(glXJoinSwapGroupSGIX),
    __ATTRIB(glXQueryCurrentRendererIntegerMESA),
    __ATTRIB(glXQueryCurrentRendererStringMESA),
    __ATTRIB(glXQueryMaxSwapBarriersSGIX),
    __ATTRIB(glXQueryRendererIntegerMESA),
    __ATTRIB(glXQueryRendererStringMESA),
    __ATTRIB(glXReleaseBuffersMESA),
    __ATTRIB(glXSwapBuffersMscOML),
    __ATTRIB(glXSwapIntervalMESA),
    __ATTRIB(glXWaitForMscOML),
    __ATTRIB(glXWaitForSbcOML),

    [DI_LAST_INDEX] = NULL,
#undef __ATTRIB
};
